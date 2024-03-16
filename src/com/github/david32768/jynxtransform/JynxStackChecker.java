package com.github.david32768.jynxtransform;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeTransform;
import java.lang.classfile.CustomAttribute;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import static java.lang.classfile.Opcode.ARRAYLENGTH;
import static java.lang.classfile.Opcode.CHECKCAST;
import static java.lang.classfile.Opcode.DCMPG;
import static java.lang.classfile.Opcode.DCMPL;
import static java.lang.classfile.Opcode.DNEG;
import static java.lang.classfile.Opcode.DUP;
import static java.lang.classfile.Opcode.DUP2;
import static java.lang.classfile.Opcode.DUP2_X1;
import static java.lang.classfile.Opcode.DUP2_X2;
import static java.lang.classfile.Opcode.DUP_X1;
import static java.lang.classfile.Opcode.DUP_X2;
import static java.lang.classfile.Opcode.FCMPG;
import static java.lang.classfile.Opcode.FCMPL;
import static java.lang.classfile.Opcode.FNEG;
import static java.lang.classfile.Opcode.GETFIELD;
import static java.lang.classfile.Opcode.GETSTATIC;
import static java.lang.classfile.Opcode.GOTO;
import static java.lang.classfile.Opcode.GOTO_W;
import static java.lang.classfile.Opcode.IFEQ;
import static java.lang.classfile.Opcode.IFGE;
import static java.lang.classfile.Opcode.IFGT;
import static java.lang.classfile.Opcode.IFLE;
import static java.lang.classfile.Opcode.IFLT;
import static java.lang.classfile.Opcode.IFNE;
import static java.lang.classfile.Opcode.IFNONNULL;
import static java.lang.classfile.Opcode.IFNULL;
import static java.lang.classfile.Opcode.INEG;
import static java.lang.classfile.Opcode.INSTANCEOF;
import static java.lang.classfile.Opcode.INVOKESTATIC;
import static java.lang.classfile.Opcode.LCMP;
import static java.lang.classfile.Opcode.LNEG;
import static java.lang.classfile.Opcode.LSHL;
import static java.lang.classfile.Opcode.LSHR;
import static java.lang.classfile.Opcode.LUSHR;
import static java.lang.classfile.Opcode.POP;
import static java.lang.classfile.Opcode.POP2;
import static java.lang.classfile.Opcode.PUTFIELD;
import static java.lang.classfile.Opcode.PUTSTATIC;
import static java.lang.classfile.Opcode.SWAP;
import java.lang.classfile.PseudoInstruction;
import java.lang.classfile.TypeKind;
import java.lang.classfile.attribute.RuntimeInvisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.RuntimeVisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.StackMapTableAttribute;
import java.lang.classfile.instruction.ArrayLoadInstruction;
import java.lang.classfile.instruction.ArrayStoreInstruction;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.CharacterRange;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.ConvertInstruction;
import java.lang.classfile.instruction.DiscontinuedInstruction;
import java.lang.classfile.instruction.ExceptionCatch;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.IncrementInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LineNumber;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LocalVariable;
import java.lang.classfile.instruction.LocalVariableType;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.MonitorInstruction;
import java.lang.classfile.instruction.NewMultiArrayInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.NewPrimitiveArrayInstruction;
import java.lang.classfile.instruction.NewReferenceArrayInstruction;
import java.lang.classfile.instruction.NopInstruction;
import java.lang.classfile.instruction.OperatorInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.lang.classfile.instruction.StoreInstruction;
import java.lang.classfile.instruction.SwitchCase;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

// Checks stack using TypeKind.Reference instead of actual Object
// assumes the stack is empty for label (if not previously used) after unconditional branch
public class JynxStackChecker implements CodeTransform {

    private final Deque<TypeKind> stack;
    private final Map<Label, Deque<TypeKind>> labelMap;
    private final List<Label> afterGotoLables;

    private boolean lastGoto;
    private final boolean debug;
    
    public JynxStackChecker() {
        this(false);
    }
    
    public JynxStackChecker(boolean debug) {
        this.stack = new ArrayDeque<>();
        this.labelMap = new HashMap<>();
        this.afterGotoLables = new ArrayList<>();
        this.lastGoto = false;
        this.debug = debug;
    }

    private void pushKind(TypeKind typeKind) {
        if (typeKind == TypeKind.VoidType) {
            return;
        }
        stack.addLast(typeKind.asLoadable());
    }
    
    private void pushInt() {
        pushKind(TypeKind.IntType);
    }
    
    private void pushReference() {
        pushKind(TypeKind.ReferenceType);
    }

    private void pushList(List<TypeKind> list) {
        for (var tos : list) {
            pushKind(tos);
        }
    }
    
    private void popKind(TypeKind typeKind) {
        if (typeKind == TypeKind.VoidType) {
            return;
        }
        TypeKind onStack = stack.removeLast();
        if (onStack != typeKind.asLoadable()) {
            String msg = String.format("top of stack is %s but expected %s",
                    onStack, typeKind.asLoadable());
            throw new IllegalArgumentException(msg);
        }
    }
    
    private void popInt() {
        popKind(TypeKind.IntType);
    }
    
    private void popReference() {
        popKind(TypeKind.ReferenceType);
    }
    
    private void popInt(int n) {
        for (int i = 0; i < n; ++i) {
            popKind(TypeKind.IntType);
        }
    }

    private TypeKind pop() {
        var tos = stack.removeLast();
        if (tos.slotSize() != 1) {
            String msg = String.format("attempting to remove single slot from stack but top of stack is %s",
                    tos);
            throw new IllegalArgumentException(msg);
        }
        return tos;
    }
    
    private List<TypeKind> pop2() {
        var tos = stack.removeLast();
        if (tos.slotSize() == 2) {
            return List.of(tos);
        }
        var nos = pop();
        return List.of(nos, tos);
    }
    
    private void branch(Label label) {
        branch(label, new ArrayDeque<>(stack));
    }
    
    private void branch(Label label, Deque<TypeKind> dq) {
        var old = labelMap.putIfAbsent(label, dq);
        if (old != null && !compare(old, stack) ) {
            String msg = String.format("mismatch stack for label, old = %s current = %s",
                    old, stack);
            throw new IllegalArgumentException(msg);
        }
    }
    
    private boolean compare(Deque<TypeKind> dq1, Deque<TypeKind> dq2) {
        return Arrays.equals(dq1.toArray(), dq2.toArray());
    }

    private void setAfter() {
        lastGoto = false;
        for (var label: afterGotoLables) {
            branch(label);
        }
        afterGotoLables.clear();
    }
    
    @Override
    public void accept(CodeBuilder builder, CodeElement element) {
        builder.with(element);
        if (debug) {
            System.err.format("%s %s%n",element, stack);
        }
        switch (element) {
            case Instruction inst -> {
                processInstruction(inst);
            }
            case PseudoInstruction pseudo -> {
                processPseudo(pseudo);
            }
            case StackMapTableAttribute _ -> {}
            case RuntimeVisibleTypeAnnotationsAttribute _ -> {}
            case RuntimeInvisibleTypeAnnotationsAttribute _ -> {}
            case CustomAttribute _ -> {}
        }
    }

    public void processPseudo(PseudoInstruction pseudo) {
        switch (pseudo) {
            case ExceptionCatch i -> {
                if (debug) {
                    System.err.format("catch handler %s%n", i.handler());
                }
                Deque<TypeKind> exdq = new ArrayDeque<>();
                exdq.add(TypeKind.ReferenceType);
                var old = labelMap.get(i.handler());
                if (old == null) {
                    branch(i.handler(), exdq);
                } else {
                    compare(old, exdq);
                }
            }
            case LabelTarget i -> {
                if (lastGoto) {
                    stack.clear();
                    var labelStack = labelMap.get(i.label());
                    if (labelStack == null) {
                        afterGotoLables.add(i.label());
                    } else {
                        stack.addAll(labelStack);
                        setAfter();
                    }
                } else{
                    branch(i.label());
                }
            }
            case CharacterRange _ -> {}
            case LineNumber _ -> {}
            case LocalVariable _ -> {}
            case LocalVariableType _ -> {}
        }
    }
    
    public void processInstruction(Instruction inst) {
        if (lastGoto) {
            if (afterGotoLables.isEmpty()) {
                String msg = String.format("instruction %s is unreachable", inst);
                throw new IllegalStateException(msg);
            }
            setAfter();
        }
        switch (inst) {
            case ArrayLoadInstruction i -> {
                popInt();
                popReference();
                pushKind(i.typeKind());
            }
            case ArrayStoreInstruction i -> {
                popKind(i.typeKind());
                popInt();
                popReference();
            }
            case BranchInstruction i -> {
                var op = i.opcode();
                var kind = op.primaryTypeKind();
                switch(op) {
                    case IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE, IFNULL, GOTO, GOTO_W -> {
                        popKind(kind);
                    }
                    case IFNONNULL -> { // BUG in java.lang.classfile.Opcode
                        popReference();
                    }
                    default -> {
                        popKind(kind);
                        popKind(kind);
                    }
                }
                branch(i.target());
            }
            case ConstantInstruction i -> {
                pushKind(i.typeKind());
            }
            case ConvertInstruction i -> {
                popKind(i.fromType());
                pushKind(i.toType());
            }
            case DiscontinuedInstruction.JsrInstruction i -> {
                pushReference();
                branch(i.target());
                popReference();
            }
            case DiscontinuedInstruction.RetInstruction _ -> {}
            case FieldInstruction i -> {
                switch(i.opcode()) {
                    case GETFIELD -> {
                        popReference();
                        pushKind(TypeKind.fromDescriptor(i.type().stringValue()));
                    }
                    case GETSTATIC -> {
                        pushKind(TypeKind.fromDescriptor(i.type().stringValue()));
                    }
                    case PUTFIELD -> {
                        popKind(TypeKind.fromDescriptor(i.type().stringValue()));
                        popReference();
                    }
                    case PUTSTATIC -> {
                        popKind(TypeKind.fromDescriptor(i.type().stringValue()));
                    }
                    default -> {
                        String msg = String.format("unknown FieldInstruction Opcode = %s",
                                i.opcode());
                        throw new AssertionError(msg);
                    }
                }
            }
            case InvokeDynamicInstruction i -> {
                var type = i.typeSymbol();
                for (var desc : type.parameterList().reversed()) {
                    var kind = TypeKind.from(desc);
                    popKind(kind);
                }
                pushKind(TypeKind.from(type.returnType()));
            }
            case InvokeInstruction i -> {
                var type = i.typeSymbol();
                for (var desc : type.parameterList().reversed()) {
                    var kind = TypeKind.from(desc);
                    popKind(kind);
                }
                switch (i.opcode()) {
                    case INVOKESTATIC -> {}
                    default -> {
                        popReference();
                    }
                }
                pushKind(TypeKind.from(type.returnType()));
            }
            case LoadInstruction i -> {
                pushKind(i.typeKind());
            }
            case StoreInstruction i -> {
                popKind(i.typeKind());
            }
            case IncrementInstruction _ -> {}
            case LookupSwitchInstruction i -> {
                popInt();
                branch(i.defaultTarget());
                for (SwitchCase switchCase : i.cases()) {
                    branch(switchCase.target());
                }
            }
            case MonitorInstruction _ -> {
                popReference();
            }
            case NewMultiArrayInstruction i -> {
                popInt(i.dimensions());
                pushReference();
            }
            case NewObjectInstruction _ -> {
                pushReference();
            }
            case NewPrimitiveArrayInstruction _ -> {
                popInt();
                pushReference();
            }
            case NewReferenceArrayInstruction _ -> {
                popInt();
                pushReference();
            }
            case NopInstruction _ -> {}
            case OperatorInstruction i -> {
                switch (i.opcode()) {
                    case ARRAYLENGTH -> {
                        popReference();
                        pushKind(i.typeKind());
                    }
                    case LSHL, LSHR, LUSHR -> {
                        popInt();
                        popKind(i.typeKind());
                        pushKind(i.typeKind());
                    }
                    case INEG, LNEG, FNEG, DNEG -> {
                        popKind(i.typeKind());
                        pushKind(i.typeKind());
                    }
                    case LCMP, FCMPG, FCMPL, DCMPG, DCMPL -> {
                        popKind(i.typeKind());
                        popKind(i.typeKind());
                        pushInt();
                    }
                    default -> {
                        popKind(i.typeKind());
                        popKind(i.typeKind());
                        pushKind(i.typeKind());
                    }
                }
                
            }
            case ReturnInstruction i -> {
                popKind(i.typeKind());
            }
            case StackInstruction i -> {
                switch(i.opcode()) {
                    case POP -> {
                        pop();
                    }    
                    case POP2 -> {
                        pop2();
                    }
                    case DUP -> {
                        var tos = pop();
                        pushKind(tos);
                        pushKind(tos);
                    }
                    case DUP_X1 -> {
                        var tos = pop();
                        var nos = pop();
                        pushKind(tos);
                        pushKind(nos);
                        pushKind(tos);
                    }
                    case DUP_X2 -> {
                        var tos = pop();
                        var list = pop2();
                        pushKind(tos);
                        pushList(list);
                        pushKind(tos);
                    }
                    case DUP2 -> {
                        var list = pop2();
                        pushList(list);
                        pushList(list);
                    }
                    case DUP2_X1 -> {
                        var toslist = pop2();
                        var nos = pop();
                        pushList(toslist);
                        pushKind(nos);
                        pushList(toslist);
                    }
                    case DUP2_X2 -> {
                        var toslist = pop2();
                        var noslist = pop2();
                        pushList(toslist);
                        pushList(noslist);
                        pushList(toslist);
                    }
                    case SWAP -> {
                        var tos = pop();
                        var nos = pop();
                        pushKind(tos);
                        pushKind(nos);
                    }
                    default -> {
                        String msg = String.format("unknown StackInstruction Opcode = %s",
                                i.opcode());
                        throw new AssertionError(msg);
                    }
                }
            }
            case TableSwitchInstruction i -> {
                popInt();
                branch(i.defaultTarget());
                for (SwitchCase switchCase : i.cases()) {
                    branch(switchCase.target());
                }
            }
            case ThrowInstruction _ -> {
                popReference();
            }
            case TypeCheckInstruction i -> {
                popReference();
                switch(i.opcode()) {
                    case INSTANCEOF -> {
                        pushInt();
                    }
                    case CHECKCAST -> {
                        pushReference();
                    }
                    default -> {
                        String msg = String.format("unknown CheckInstruction Opcode = %s",
                                i.opcode());
                        throw new AssertionError(msg);
                    }
                }
            }
        }
        lastGoto = inst.opcode().isUnconditionalBranch();
    }

    @Override
    public void atStart(CodeBuilder builder) {
        if (debug) {
            System.err.println("****** start called");
        }
        stack.clear();
        labelMap.clear();
        afterGotoLables.clear();
        lastGoto = false;
    }

    @Override
    public void atEnd(CodeBuilder builder) {
    }
    
}
