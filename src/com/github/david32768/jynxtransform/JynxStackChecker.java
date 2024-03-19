package com.github.david32768.jynxtransform;

import static java.lang.classfile.Opcode.*;
import java.lang.classfile.instruction.*;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeTransform;
import java.lang.classfile.CustomAttribute;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.Opcode;
import java.lang.classfile.PseudoInstruction;
import java.lang.classfile.TypeKind;
import java.lang.classfile.attribute.RuntimeInvisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.RuntimeVisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.StackMapTableAttribute;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

// Checks stack using TypeKind.Reference instead of actual Object
//     assumes the stack is empty for label (if not previously used) after unconditional branch
//     but can add unreachable xCONST_0 before this label to define non-empty stack
//     these unreachable instructions will be dropped.
public class JynxStackChecker implements CodeTransform {

    private final Deque<TypeKind> stack;
    private final Map<Label, Deque<TypeKind>> labelMap;
    private final List<Label> afterGotoLables;

    private final boolean trace;
    private boolean lastGoto;
    private boolean drop; 
    
    public JynxStackChecker() {
        this(false);
    }
    
    public JynxStackChecker(boolean trace) {
        this.stack = new ArrayDeque<>();
        this.labelMap = new HashMap<>();
        this.afterGotoLables = new ArrayList<>();
        this.lastGoto = false;
        this.trace = trace;
        this.drop = false;
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
    public void atStart(CodeBuilder builder) {
        if (trace) {
            System.err.println("****** start called");
        }
        stack.clear();
        labelMap.clear();
        afterGotoLables.clear();
        lastGoto = false;
        drop = false;
    }

    @Override
    public void atEnd(CodeBuilder builder) {
    }
    
    @Override
    public void accept(CodeBuilder builder, CodeElement element) {
        drop = false;
        if (trace) {
            System.err.format("stack: %s%n", stack);
            System.err.format("element: %s%n",element);
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
        if (drop) {
            if (trace) {
                System.err.format("drop: %s%n", element);
            }
        } else {
            builder.with(element);
        }
    }

    private void processPseudo(PseudoInstruction pseudo) {
        switch (pseudo) {
            case ExceptionCatch i -> {
                if (trace) {
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
                if (lastGoto && stack.isEmpty()) {
                    var labelStack = labelMap.get(i.label());
                    if (labelStack == null) {
                        afterGotoLables.add(i.label());
                    } else {
                        stack.addAll(labelStack);
                        setAfter();
                    }
                } else {
                    if (lastGoto) {
                        lastGoto = false;
                    }
                    branch(i.label());
                }
            }
            case CharacterRange _ -> {}
            case LineNumber _ -> {}
            case LocalVariable _ -> {}
            case LocalVariableType _ -> {}
        }
    }
    
    private void processInstruction(Instruction inst) {
        if (lastGoto) {
            if (afterGotoLables.isEmpty()) {
                switch(inst.opcode()) {
                    case ICONST_0, FCONST_0, LCONST_0, DCONST_0, ACONST_NULL -> {
                        pushKind(inst.opcode().primaryTypeKind());
                        drop =  true;
                        return;
                    }
                    default -> {
                        String msg = String.format("instruction %s is unreachable", inst);
                        throw new IllegalStateException(msg);
                    }
                }
            }
            setAfter();
        }
        adjustStackForInstruction(inst);
        if (inst.opcode().isUnconditionalBranch()) {
            lastGoto = true;
            stack.clear();
        }
    }
    
    private static final String BAD_OP = "misclassified or unknown op - ";
    private static final String MISSING = "missing case for op - ";
    
    private void adjustStackForInstruction(Instruction inst) {
        var op = inst.opcode();
        switch (inst) {
            case ArrayLoadInstruction i -> {
                assert EnumSet.of(IALOAD, LALOAD, FALOAD, DALOAD, AALOAD, BALOAD, CALOAD, SALOAD)
                    .contains(op):BAD_OP + op;
                popInt();
                popReference();
                pushKind(i.typeKind());
            }
            case ArrayStoreInstruction i -> {
                assert EnumSet.of(IASTORE, LASTORE, FASTORE, DASTORE, AASTORE, BASTORE, CASTORE, SASTORE)
                    .contains(op):BAD_OP + op;
                popKind(i.typeKind());
                popInt();
                popReference();
            }
            case BranchInstruction i -> {
                assert EnumSet.of(IFEQ, IFNE, IFLT, IFGE, IFGT, IFLE, IFNULL, IFNONNULL,
                        IF_ICMPEQ, IF_ICMPNE, IF_ICMPLT, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE, IF_ACMPEQ, IF_ACMPNE,
                        GOTO, GOTO_W)
                    .contains(op):BAD_OP + op;
                var kind = op.primaryTypeKind();
                switch(op) {
                    case IFNONNULL -> { // BUG in java.lang.classfile.Opcode
                        kind = TypeKind.ReferenceType;
                    }
                    case IF_ICMPEQ, IF_ICMPNE, IF_ICMPLT, IF_ICMPGT, IF_ICMPGE, IF_ICMPLE, IF_ACMPEQ, IF_ACMPNE -> {
                        popKind(kind);
                    }
                    default -> {
                        assert EnumSet.of(IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE, IFNULL, GOTO, GOTO_W)
                                .contains(op):MISSING + op;
                    }
                }
                popKind(kind);
                branch(i.target());
            }
            case ConstantInstruction i -> {
                assert EnumSet.of(ACONST_NULL, BIPUSH, SIPUSH, LDC, LDC_W, LDC2_W,
                        ICONST_M1, ICONST_0, ICONST_1, ICONST_2, ICONST_3, ICONST_4, ICONST_5,
                        LCONST_0, LCONST_1, FCONST_0, FCONST_1, FCONST_2, DCONST_0, DCONST_1)
                    .contains(op):BAD_OP + op;
                pushKind(i.typeKind());
            }
            case ConvertInstruction i -> {
                assert EnumSet.of(I2L, I2F, I2D, L2I, L2F, L2D, F2I, F2L, F2D, D2I, D2L, D2F, I2B, I2C, I2S)
                        .contains(op):BAD_OP + op;
                popKind(i.fromType());
                pushKind(i.toType());
            }
            case DiscontinuedInstruction.JsrInstruction i -> {
                assert EnumSet.of(JSR, JSR_W).contains(op):BAD_OP + op;
                pushReference();
                branch(i.target());
                popReference();
            }
            case DiscontinuedInstruction.RetInstruction _ -> {
                assert EnumSet.of(RET, RET_W).contains(op):BAD_OP + op;
            }
            case FieldInstruction i -> {
                assert EnumSet.of(GETSTATIC, PUTSTATIC, GETFIELD, PUTFIELD).contains(op):BAD_OP + op;
                var kind = TypeKind.from(i.typeSymbol());
                switch(op) {
                    case GETFIELD -> {
                        popReference();
                        pushKind(kind);
                    }
                    case GETSTATIC -> {
                        pushKind(kind);
                    }
                    case PUTFIELD -> {
                        popKind(kind);
                        popReference();
                    }
                    case PUTSTATIC -> {
                        popKind(kind);
                    }
                    default -> {
                        assert false:MISSING + op;
                    }
                }
            }
            case InvokeDynamicInstruction i -> {
                assert op == Opcode.INVOKEDYNAMIC:BAD_OP + op;
                var type = i.typeSymbol();
                for (var desc : type.parameterList().reversed()) {
                    var kind = TypeKind.from(desc);
                    popKind(kind);
                }
                pushKind(TypeKind.from(type.returnType()));
            }
            case InvokeInstruction i -> {
                assert EnumSet.of(INVOKEVIRTUAL, INVOKESPECIAL, INVOKESTATIC, INVOKEINTERFACE)
                    .contains(op):BAD_OP + op;
                var type = i.typeSymbol();
                for (var desc : type.parameterList().reversed()) {
                    var kind = TypeKind.from(desc);
                    popKind(kind);
                }
                switch (op) {
                    case INVOKEINTERFACE, INVOKESPECIAL, INVOKEVIRTUAL -> {
                        popReference();
                    }
                    default -> {
                        assert op == Opcode.INVOKESTATIC:MISSING + op;
                    }
                }
                pushKind(TypeKind.from(type.returnType()));
            }
            case LoadInstruction i -> {
                assert EnumSet.of(ILOAD, LLOAD, FLOAD, DLOAD, ALOAD,
                        ILOAD_0, ILOAD_1, ILOAD_2, ILOAD_3,
                        LLOAD_0, LLOAD_1, LLOAD_2, LLOAD_3,
                        FLOAD_0, FLOAD_1, FLOAD_2, FLOAD_3,
                        DLOAD_0, DLOAD_1, DLOAD_2, DLOAD_3,
                        ALOAD_0, ALOAD_1, ALOAD_2, ALOAD_3,
                        ILOAD_W, LLOAD_W, FLOAD_W, DLOAD_W, ALOAD_W)
                    .contains(op):BAD_OP + op;
                pushKind(i.typeKind());
            }
            case StoreInstruction i -> {
                assert EnumSet.of(ISTORE, LSTORE, FSTORE, DSTORE, ASTORE,
                        ISTORE_0, ISTORE_1, ISTORE_2, ISTORE_3,
                        LSTORE_0, LSTORE_1, LSTORE_2, LSTORE_3,
                        FSTORE_0, FSTORE_1, FSTORE_2, FSTORE_3,
                        DSTORE_0, DSTORE_1, DSTORE_2, DSTORE_3,
                        ASTORE_0, ASTORE_1, ASTORE_2, ASTORE_3,
                        ISTORE_W, LSTORE_W, FSTORE_W, DSTORE_W, ASTORE_W)
                    .contains(op):BAD_OP + op;
                popKind(i.typeKind());
            }
            case IncrementInstruction _ -> {
                assert EnumSet.of(IINC, IINC_W).contains(op):BAD_OP + op;
            }
            case LookupSwitchInstruction i -> {
                assert op == Opcode.LOOKUPSWITCH:BAD_OP + op;
                popInt();
                branch(i.defaultTarget());
                for (SwitchCase switchCase : i.cases()) {
                    branch(switchCase.target());
                }
            }
            case MonitorInstruction _ -> {
                assert EnumSet.of(MONITORENTER, MONITOREXIT).contains(op):BAD_OP + op;
                popReference();
            }
            case NewMultiArrayInstruction i -> {
                assert op == Opcode.MULTIANEWARRAY:BAD_OP + op;
                popInt(i.dimensions());
                pushReference();
            }
            case NewObjectInstruction _ -> {
                assert op == Opcode.NEW:BAD_OP + op;
                pushReference();
            }
            case NewPrimitiveArrayInstruction _ -> {
                assert op == Opcode.NEWARRAY:BAD_OP + op;
                popInt();
                pushReference();
            }
            case NewReferenceArrayInstruction _ -> {
                assert op == Opcode.ANEWARRAY:BAD_OP + op;
                popInt();
                pushReference();
            }
            case NopInstruction _ -> {
                assert op == Opcode.NOP:BAD_OP + op;
            }
            case OperatorInstruction i -> {
                assert EnumSet.of(IADD, LADD, FADD, DADD,
                        ISUB, LSUB, FSUB, DSUB,
                        IMUL, LMUL, FMUL, DMUL,
                        IDIV, LDIV, FDIV, DDIV,
                        IREM, LREM, FREM, DREM,
                        INEG, LNEG, FNEG, DNEG,
                        ISHL, LSHL, ISHR, LSHR, IUSHR, LUSHR,
                        IAND, LAND, IOR, LOR, IXOR, LXOR,
                        LCMP, FCMPL, FCMPG, DCMPL, DCMPG,
                        ARRAYLENGTH)
                    .contains(op):BAD_OP + op;
                var kind = i.typeKind();
                var result = kind;
                switch (op) {
                    case ARRAYLENGTH -> {
                        popReference();
                    }
                    case ISHL, ISHR, IUSHR, LSHL, LSHR, LUSHR -> {
                        popInt();
                        popKind(kind);
                    }
                    case INEG, LNEG, FNEG, DNEG -> {
                        popKind(kind);
                    }
                    case LCMP, FCMPG, FCMPL, DCMPG, DCMPL -> {
                        popKind(kind);
                        popKind(kind);
                        result = TypeKind.IntType;
                    }
                    case IADD, LADD, FADD, DADD,
                            ISUB, LSUB, FSUB, DSUB,
                            IMUL, LMUL, FMUL, DMUL,
                            IDIV, LDIV, FDIV, DDIV,
                            IREM, LREM, FREM, DREM,
                            IAND, LAND, IOR, LOR, IXOR, LXOR
                               -> {
                        popKind(kind);
                        popKind(kind);
                    }
                    default -> {
                        assert false:MISSING + op;
                    }
                }
                pushKind(result);
            }
            case ReturnInstruction i -> {
                assert EnumSet.of(IRETURN, LRETURN, FRETURN, DRETURN, ARETURN, RETURN)
                    .contains(op):BAD_OP + op;
                popKind(i.typeKind());
            }
            case StackInstruction _ -> {
                assert EnumSet.of(POP, POP2, DUP, DUP_X1, DUP_X2, DUP2, DUP2_X1, DUP2_X2, SWAP)
                    .contains(op):BAD_OP + op;
                switch(op) {
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
                        assert false:MISSING + op;
                    }
                }
            }
            case TableSwitchInstruction i -> {
                assert op == Opcode.TABLESWITCH:BAD_OP + op;
                popInt();
                branch(i.defaultTarget());
                for (SwitchCase switchCase : i.cases()) {
                    branch(switchCase.target());
                }
            }
            case ThrowInstruction _ -> {
                assert op == Opcode.ATHROW:BAD_OP + op;
                popReference();
            }
            case TypeCheckInstruction _ -> {
                assert EnumSet.of(INSTANCEOF, CHECKCAST).contains(op):BAD_OP + op;
                popReference();
                switch(op) {
                    case INSTANCEOF -> {
                        pushInt();
                    }
                    case CHECKCAST -> {
                        pushReference();
                    }
                    default -> {
                        assert false:MISSING + op;
                    }
                }
            }
        }
    }

}
