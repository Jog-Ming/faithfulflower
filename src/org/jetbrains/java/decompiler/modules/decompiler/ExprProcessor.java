// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler;

import org.jetbrains.annotations.Nullable;
import org.jetbrains.java.decompiler.api.Decompiler;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.StatementWriter;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.InstructionSequence;
import org.jetbrains.java.decompiler.code.MethodProperties;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdgeType;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectNode;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructContext;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructBootstrapMethodsAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructConstantValueAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructNestHostAttribute;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.util.*;

public class ExprProcessor implements CodeConstants {
  public static final String UNDEFINED_TYPE_STRING = "<undefinedtype>";
  public static final String UNREPRESENTABLE_TYPE_STRING = "<unrepresentable>";
  public static final String UNKNOWN_TYPE_STRING = "<unknown>";
  public static final String NULL_TYPE_STRING = "<null>";

  private static final Map<Integer, FunctionType> mapConsts = new HashMap<>();
  static {
    mapConsts.put(opc_arraylength, FunctionType.ARRAY_LENGTH);
    mapConsts.put(opc_checkcast, FunctionType.CAST);
    mapConsts.put(opc_instanceof, FunctionType.INSTANCEOF);
  }

  private static final VarType[] consts = {
    VarType.VARTYPE_INT, VarType.VARTYPE_FLOAT, VarType.VARTYPE_LONG, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_CLASS, VarType.VARTYPE_STRING,
    VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID, VarType.VARTYPE_VOID,
    VarType.VARTYPE_VOID, VarType.VARTYPE_METHODTYPE
  };

  private static final VarType[] varTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT
  };

  private static final VarType[] arrTypes = {
    VarType.VARTYPE_INT, VarType.VARTYPE_LONG, VarType.VARTYPE_FLOAT, VarType.VARTYPE_DOUBLE, VarType.VARTYPE_OBJECT,
    VarType.VARTYPE_BOOLEAN, VarType.VARTYPE_CHAR, VarType.VARTYPE_SHORT
  };

  private static final FunctionType[] func1 = {
    FunctionType.ADD, FunctionType.SUB, FunctionType.MUL, FunctionType.DIV,
    FunctionType.REM
  };
  private static final FunctionType[] func2 = {
    FunctionType.SHL, FunctionType.SHR, FunctionType.USHR, FunctionType.AND,
    FunctionType.OR, FunctionType.XOR
  };
  private static final FunctionType[] func3 = {
    FunctionType.I2L, FunctionType.I2F, FunctionType.I2D, FunctionType.L2I,
    FunctionType.L2F, FunctionType.L2D, FunctionType.F2I, FunctionType.F2L,
    FunctionType.F2D, FunctionType.D2I, FunctionType.D2L, FunctionType.D2F,
    FunctionType.I2B, FunctionType.I2C, FunctionType.I2S
  };
  private static final FunctionType[] func4 = {
    FunctionType.LCMP, FunctionType.FCMPL, FunctionType.FCMPG, FunctionType.DCMPL,
    FunctionType.DCMPG
  };
  private static final IfExprent.Type[] func5 = {
    IfExprent.Type.EQ, IfExprent.Type.NE, IfExprent.Type.LT, IfExprent.Type.GE, IfExprent.Type.GT, IfExprent.Type.LE
  };
  private static final IfExprent.Type[] func6 = {
    IfExprent.Type.ICMPEQ, IfExprent.Type.ICMPNE, IfExprent.Type.ICMPLT, IfExprent.Type.ICMPGE, IfExprent.Type.ICMPGT, IfExprent.Type.ICMPLE,
    IfExprent.Type.ACMPEQ, IfExprent.Type.ACMPNE
  };
  private static final IfExprent.Type[] func7 = {IfExprent.Type.NULL, IfExprent.Type.NONNULL};
  private static final MonitorExprent.Type[] func8 = {MonitorExprent.Type.ENTER, MonitorExprent.Type.EXIT};

  private static final CodeType[] arrTypeIds = {
    CodeType.BOOLEAN, CodeType.CHAR, CodeType.FLOAT, CodeType.DOUBLE,
    CodeType.BYTE, CodeType.SHORT, CodeType.INT, CodeType.LONG
  };

  private static final String[] typeNames = {"byte", "char", "double", "float", "int", "long", "short", "boolean"};

  private final MethodDescriptor methodDescriptor;
  private final VarProcessor varProcessor;

  public ExprProcessor(MethodDescriptor md, VarProcessor varProc) {
    methodDescriptor = md;
    varProcessor = varProc;
  }

  public void processStatement(RootStatement root, StructClass cl) {
    FlattenStatementsHelper flatHelper = new FlattenStatementsHelper();
    DirectGraph dgraph = flatHelper.buildDirectGraph(root);

    ValidationHelper.validateDGraph(dgraph, root);

    // TODO: use DirectNode instead DirectNode.id
    Map<String, VarExprent> mapCatch = new HashMap<>();
    collectCatchVars(root, flatHelper, mapCatch);

    Map<DirectNode, PrimitiveExprsList> mapData = new HashMap<>();

    ListStack<DirectNode> stack = new ListStack<>();

    stack.push(dgraph.first);
    mapData.put(dgraph.first, new PrimitiveExprsList());

    while (!stack.isEmpty()) {

      DirectNode node = stack.pop();

      PrimitiveExprsList data;
      if (mapCatch.containsKey(node.id)) {
        data = getExpressionData(mapCatch.get(node.id));
      } else {
        data = mapData.get(node);
      }

      BasicBlockStatement block = node.block;
      if (block != null) {
        processBlock(block, data, cl);
        block.setExprents(data.getLstExprents());
      }

      // TODO: is this copying the stack into catch and finally blocks? It shouldn't do that.
      for (var cd : node.getSuccessors(DirectEdgeType.REGULAR)) {
        DirectNode nd = cd.getDestination();
        if (!mapData.containsKey(nd)) {
          mapData.put(nd, copyVarExprents(data.copyStack()));
          stack.add(nd);
        }
      }
    }

    initStatementExprents(root);
  }

  private static PrimitiveExprsList copyVarExprents(PrimitiveExprsList data) {
    ListStack<Exprent> stack = data.getStack();
    copyEntries(stack);
    return data;
  }

  public static void copyEntries(List<Exprent> stack) {
    for (int i = 0; i < stack.size(); i++) {
      stack.set(i, stack.get(i).copy());
    }
  }

  private static void collectCatchVars(Statement stat, FlattenStatementsHelper flatthelper, Map<String, VarExprent> map) {

    List<VarExprent> lst = null;

    if (stat instanceof CatchAllStatement) {
      CatchAllStatement catchall = (CatchAllStatement)stat;
      if (!catchall.isFinally()) {
        lst = catchall.getVars();
      }
    }
    else if (stat instanceof CatchStatement) {
      lst = ((CatchStatement)stat).getVars();
    }

    if (lst != null) {
      for (int i = 1; i < stat.getStats().size(); i++) {
        map.put(flatthelper.getDirectNode(stat.getStats().get(i)).id, lst.get(i - 1));
      }
    }

    for (Statement st : stat.getStats()) {
      collectCatchVars(st, flatthelper, map);
    }
  }

  private static void initStatementExprents(Statement stat) {
    stat.initExprents();

    for (Statement st : stat.getStats()) {
      initStatementExprents(st);
    }
  }

  public void processBlock(BasicBlockStatement stat, PrimitiveExprsList data, StructClass cl) {

    ConstantPool pool = cl.getPool();
    StructBootstrapMethodsAttribute bootstrap = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS);

    BasicBlock block = stat.getBlock();

    ListStack<Exprent> stack = data.getStack();
    List<Exprent> exprlist = data.getLstExprents();

    InstructionSequence seq = block.getSeq();

    // A constant variable read through a qualifying expression leaves only the qualifier's null
    // check in the class file: javac inlines the value at the access site. The constant push right
    // after the check is replaced by the field access it stands for.
    Exprent pendingFieldAccess = null;
    int pendingFieldIndex = -1;

    // The value a `pop` discarded, waiting for the static call whose arguments start at the stack
    // depth it was popped from: that value is the source's qualifier of a static member access
    // written through an expression, and javac evaluates it only for its side effects.
    Exprent pendingStaticQualifier = null;
    int pendingStaticDepth = -1;

    for (int i = 0; i < seq.length(); i++) {

      Instruction instr = seq.getInstr(i);
      int bytecode_offset = instr.startOffset;
      BitSet bytecode_offsets = null;
      if (bytecode_offset >= 0) {
        bytecode_offsets = new BitSet();
        bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
      }

      if (i == pendingFieldIndex) {
        pendingFieldAccess.addBytecodeOffsets(bytecode_offsets);
        pushEx(stack, exprlist, pendingFieldAccess);
        pendingFieldAccess = null;
        pendingFieldIndex = -1;
        continue;
      }

      switch (instr.opcode) {
        case opc_aconst_null:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_NULL, null, bytecode_offsets));
          break;
        case opc_bipush:
        case opc_sipush:
          pushEx(stack, exprlist, new ConstExprent(instr.operand(0), true, bytecode_offsets));
          break;
        case opc_lconst_0:
        case opc_lconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_LONG, (long)(instr.opcode - opc_lconst_0), bytecode_offsets));
          break;
        case opc_fconst_0:
        case opc_fconst_1:
        case opc_fconst_2:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_FLOAT, (float)(instr.opcode - opc_fconst_0), bytecode_offsets));
          break;
        case opc_dconst_0:
        case opc_dconst_1:
          pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_DOUBLE, (double)(instr.opcode - opc_dconst_0), bytecode_offsets));
          break;
        case opc_ldc:
        case opc_ldc_w:
        case opc_ldc2_w:
          PooledConstant cn = pool.getConstant(instr.operand(0));
          if (cn instanceof PrimitiveConstant) {
            pushEx(stack, exprlist, new ConstExprent(consts[cn.type - CONSTANT_Integer], ((PrimitiveConstant)cn).value, bytecode_offsets));
          }
          else if (cn instanceof LinkConstant && cn.type == CodeConstants.CONSTANT_Dynamic) {
            LinkConstant invoke_constant = (LinkConstant) cn;

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, CondyHelper.simplifyCondy(exprinv));
            }
          }
          else if (cn instanceof LinkConstant) {
            //TODO: for now treat Links as Strings
            pushEx(stack, exprlist, new ConstExprent(VarType.VARTYPE_STRING, ((LinkConstant)cn).elementname, bytecode_offsets));
          }
          break;
        case opc_iload:
        case opc_lload:
        case opc_fload:
        case opc_dload:
        case opc_aload:
          VarExprent varExprent = new VarExprent(instr.operand(0), varTypes[instr.opcode - opc_iload], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          pushEx(stack, exprlist, varExprent);
          break;
        case opc_iaload:
        case opc_laload:
        case opc_faload:
        case opc_daload:
        case opc_aaload:
        case opc_baload:
        case opc_caload:
        case opc_saload:
          Exprent index = stack.pop();
          Exprent arr = stack.pop();

          VarType vartype = null;
          switch (instr.opcode) {
            case opc_laload:
              vartype = VarType.VARTYPE_LONG;
              break;
            case opc_daload:
              vartype = VarType.VARTYPE_DOUBLE;
          }
          pushEx(stack, exprlist, new ArrayExprent(arr, index, arrTypes[instr.opcode - opc_iaload], bytecode_offsets), vartype);
          break;
        case opc_istore:
        case opc_lstore:
        case opc_fstore:
        case opc_dstore:
        case opc_astore:
          Exprent expr = stack.pop();
          int varindex = instr.operand(0);
          if (bytecode_offsets != null) { //TODO: Figure out why this nulls in some cases
            bytecode_offsets.set(bytecode_offset, bytecode_offset + instr.length);
          }
          varExprent = new VarExprent(varindex, varTypes[instr.opcode - opc_istore], varProcessor, bytecode_offsets);
          varExprent.setBackingInstr(instr);
          varProcessor.findLVT(varExprent, bytecode_offset + instr.length);
          AssignmentExprent assign = new AssignmentExprent(varExprent, expr, bytecode_offsets);
          exprlist.add(assign);
          break;
        case opc_iastore:
        case opc_lastore:
        case opc_fastore:
        case opc_dastore:
        case opc_aastore:
        case opc_bastore:
        case opc_castore:
        case opc_sastore:
          Exprent value = stack.pop();
          Exprent index_store = stack.pop();
          Exprent arr_store = stack.pop();
          AssignmentExprent arrassign =
            new AssignmentExprent(new ArrayExprent(arr_store, index_store, arrTypes[instr.opcode - opc_iastore], bytecode_offsets), value,
                                  bytecode_offsets);
          exprlist.add(arrassign);
          break;
        case opc_iadd:
        case opc_ladd:
        case opc_fadd:
        case opc_dadd:
        case opc_isub:
        case opc_lsub:
        case opc_fsub:
        case opc_dsub:
        case opc_imul:
        case opc_lmul:
        case opc_fmul:
        case opc_dmul:
        case opc_idiv:
        case opc_ldiv:
        case opc_fdiv:
        case opc_ddiv:
        case opc_irem:
        case opc_lrem:
        case opc_frem:
        case opc_drem:
          pushEx(stack, exprlist, new FunctionExprent(func1[(instr.opcode - opc_iadd) / 4], stack, bytecode_offsets));
          break;
        case opc_ishl:
        case opc_lshl:
        case opc_ishr:
        case opc_lshr:
        case opc_iushr:
        case opc_lushr:
        case opc_iand:
        case opc_land:
        case opc_ior:
        case opc_lor:
        case opc_ixor:
        case opc_lxor:
          pushEx(stack, exprlist, new FunctionExprent(func2[(instr.opcode - opc_ishl) / 2], stack, bytecode_offsets));
          break;
        case opc_ineg:
        case opc_lneg:
        case opc_fneg:
        case opc_dneg:
          pushEx(stack, exprlist, new FunctionExprent(FunctionType.NEG, stack, bytecode_offsets));
          break;
        case opc_iinc:
          VarExprent vevar = new VarExprent(instr.operand(0), VarType.VARTYPE_INT, varProcessor, bytecode_offsets);
          vevar.setBackingInstr(instr);
          varProcessor.findLVT(vevar, bytecode_offset + instr.length);
          exprlist.add(new AssignmentExprent(vevar, new FunctionExprent(
            instr.operand(1) < 0 ? FunctionType.SUB : FunctionType.ADD, Arrays
            .asList(vevar.copy(), new ConstExprent(VarType.VARTYPE_INT, Math.abs(instr.operand(1)), null)),
            bytecode_offsets), bytecode_offsets));
          break;
        case opc_i2l:
        case opc_i2f:
        case opc_i2d:
        case opc_l2i:
        case opc_l2f:
        case opc_l2d:
        case opc_f2i:
        case opc_f2l:
        case opc_f2d:
        case opc_d2i:
        case opc_d2l:
        case opc_d2f:
        case opc_i2b:
        case opc_i2c:
        case opc_i2s:
          pushEx(stack, exprlist, new FunctionExprent(func3[instr.opcode - opc_i2l], stack, bytecode_offsets));
          break;
        case opc_lcmp:
        case opc_fcmpl:
        case opc_fcmpg:
        case opc_dcmpl:
        case opc_dcmpg:
          pushEx(stack, exprlist, new FunctionExprent(func4[instr.opcode - opc_lcmp], stack, bytecode_offsets));
          break;
        case opc_ifeq:
        case opc_ifne:
        case opc_iflt:
        case opc_ifge:
        case opc_ifgt:
        case opc_ifle:
          exprlist.add(new IfExprent(func5[instr.opcode - opc_ifeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_if_icmpeq:
        case opc_if_icmpne:
        case opc_if_icmplt:
        case opc_if_icmpge:
        case opc_if_icmpgt:
        case opc_if_icmple:
        case opc_if_acmpeq:
        case opc_if_acmpne:
          exprlist.add(new IfExprent(func6[instr.opcode - opc_if_icmpeq].getNegative(), stack, bytecode_offsets));
          break;
        case opc_ifnull:
        case opc_ifnonnull:
          exprlist.add(new IfExprent(func7[instr.opcode - opc_ifnull].getNegative(), stack, bytecode_offsets));
          break;
        case opc_tableswitch:
        case opc_lookupswitch:
          exprlist.add(new SwitchHeadExprent(stack.pop(), bytecode_offsets));
          break;
        case opc_ireturn:
        case opc_lreturn:
        case opc_freturn:
        case opc_dreturn:
        case opc_areturn:
        case opc_return:
        case opc_athrow:
          exprlist.add(new ExitExprent(instr.opcode == opc_athrow ? ExitExprent.Type.THROW : ExitExprent.Type.RETURN,
                                       instr.opcode == opc_return ? null : stack.pop(),
                                       instr.opcode == opc_athrow ? null : methodDescriptor.ret,
                                       bytecode_offsets, methodDescriptor));
          break;
        case opc_monitorenter:
        case opc_monitorexit:
          MonitorExprent monitor = new MonitorExprent(func8[instr.opcode - opc_monitorenter], stack.pop(), bytecode_offsets);

          if (instr.opcode == opc_monitorexit && stat.isRemovableMonitorexit()) {
            monitor.setRemove(true);
          }

          exprlist.add(monitor);
          break;
        case opc_checkcast:
        case opc_instanceof:
          stack.push(new ConstExprent(new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true), null, null));
        case opc_arraylength:
          FunctionExprent recorded = new FunctionExprent(mapConsts.get(instr.opcode), stack, bytecode_offsets);
          if (instr.opcode == opc_checkcast) {
            recorded.setRecordedCheckcast();
          }
          pushEx(stack, exprlist, recorded);
          break;
        case opc_getstatic:
        case opc_getfield:
          FieldExprent readField = new FieldExprent(pool.getLinkConstant(instr.operand(0)),
            instr.opcode == opc_getstatic ? null : stack.pop(), bytecode_offsets);
          if (instr.opcode == opc_getstatic && pendingStaticQualifier != null
              && stack.size() == pendingStaticDepth) {
            // The value popped right before this read is the expression the source wrote before
            // the static field (`itemStatsList.BLOCK_COLUMNS`): javac evaluates it only for its
            // side effects, and printing the class name instead would drop the load.
            readField.setInstance(pendingStaticQualifier);
            pendingStaticQualifier = null;
            pendingStaticDepth = -1;
          }
          pushEx(stack, exprlist, readField);
          break;
        case opc_putstatic:
        case opc_putfield:
          Exprent valfield = stack.pop();
          Exprent exprfield =
            new FieldExprent(pool.getLinkConstant(instr.operand(0)), instr.opcode == opc_putstatic ? null : stack.pop(),
                             bytecode_offsets);
          exprlist.add(new AssignmentExprent(exprfield, valfield, bytecode_offsets));
          break;
        case opc_invokevirtual:
        case opc_invokespecial:
        case opc_invokestatic:
        case opc_invokeinterface:
        case opc_invokedynamic:
          if (instr.opcode != opc_invokedynamic || instr.bytecodeVersion.hasInvokeDynamic()) {
            LinkConstant invoke_constant = pool.getLinkConstant(instr.operand(0));

            LinkConstant bootstrapMethod = null;
            List<PooledConstant> bootstrap_arguments = null;
            if (instr.opcode == opc_invokedynamic && bootstrap != null) {
              bootstrapMethod = bootstrap.getMethodReference(invoke_constant.index1);
              bootstrap_arguments = bootstrap.getMethodArguments(invoke_constant.index1);
            }

            InvocationExprent exprinv = new InvocationExprent(instr.opcode, invoke_constant, bootstrapMethod, bootstrap_arguments, stack, bytecode_offsets);
            if (instr.opcode == opc_invokestatic && pendingStaticQualifier != null
                && stack.size() == pendingStaticDepth) {
              // This call's arguments start at the depth the discarded value was popped from:
              // the value is the call's qualifier, evaluated by javac only for its side effects.
              exprinv.setStaticQualifier(pendingStaticQualifier);
              pendingStaticQualifier = null;
              pendingStaticDepth = -1;
            }
            if (exprinv.getDescriptor().ret.type == CodeType.VOID) {
              exprlist.add(exprinv);
            }
            else {
              pushEx(stack, exprlist, exprinv);
            }
          }
          break;
        case opc_new:
        case opc_anewarray:
        case opc_multianewarray:
          int dimensions = (instr.opcode == opc_new) ? 0 : (instr.opcode == opc_anewarray) ? 1 : instr.operand(1);
          VarType arrType = new VarType(pool.getPrimitiveConstant(instr.operand(0)).getString(), true);
          if (instr.opcode != opc_multianewarray) {
            arrType = arrType.resizeArrayDim(arrType.arrayDim + dimensions);
          }
          pushEx(stack, exprlist, new NewExprent(arrType, stack, dimensions, bytecode_offsets));
          break;
        case opc_newarray:
          pushEx(stack, exprlist, new NewExprent(new VarType(arrTypeIds[instr.operand(0) - 4], 1), stack, 1, bytecode_offsets));
          break;
        case opc_dup:
          pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          break;
        case opc_dup_x1:
          insertByOffsetEx(-2, stack, exprlist, -1);
          break;
        case opc_dup_x2:
          if (stack.getByOffset(-2).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            pushEx(stack, exprlist, stack.getByOffset(-1).copy());
          }
          else {
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
            pushEx(stack, exprlist, stack.getByOffset(-2).copy());
          }
          break;
        case opc_dup2_x1:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            insertByOffsetEx(-2, stack, exprlist, -1);
          }
          else {
            insertByOffsetEx(-3, stack, exprlist, -2);
            insertByOffsetEx(-3, stack, exprlist, -1);
          }
          break;
        case opc_dup2_x2:
          if (stack.getByOffset(-1).getExprType().stackSize == 2) {
            if (stack.getByOffset(-2).getExprType().stackSize == 2) {
              insertByOffsetEx(-2, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
          }
          else {
            if (stack.getByOffset(-3).getExprType().stackSize == 2) {
              insertByOffsetEx(-3, stack, exprlist, -2);
              insertByOffsetEx(-3, stack, exprlist, -1);
            }
            else {
              insertByOffsetEx(-4, stack, exprlist, -2);
              insertByOffsetEx(-4, stack, exprlist, -1);
            }
          }
          break;
        case opc_swap:
          insertByOffsetEx(-2, stack, exprlist, -1);
          stack.pop();
          break;
        case opc_pop:
          Exprent discarded = staticQualifierValue(exprlist, stack);
          stack.pop();
          if (discarded != null) {
            pendingStaticQualifier = discarded;
            pendingStaticDepth = stack.size();
          }
          // check for synthetic getClass and requireNonNull calls added by the compiler
          // see https://stackoverflow.com/a/20130641
          if (!exprlist.isEmpty()) {
            Exprent last = exprlist.get(exprlist.size() - 1);
            // Our heuristic is checking for an assignment and the type of the assignment is an invocation.
            // This roughly corresponds to a pattern of DUP [nullcheck] POP.
            if (last instanceof AssignmentExprent && ((AssignmentExprent)last).getRight() instanceof InvocationExprent) {
              InvocationExprent invocation = (InvocationExprent) ((AssignmentExprent) last).getRight();

              // Check to make sure there's still more opcodes after this one
              if (i + 1 < seq.length()) {
                // Match either this.getClass() or Objects.requireNonNull([value]);
                if ((!invocation.isStatic() && invocation.getName().equals("getClass") && invocation.getStringDescriptor().equals("()Ljava/lang/Class;")) // J8
                  || (invocation.isStatic() && invocation.getClassname().equals("java/util/Objects") && invocation.getName().equals("requireNonNull") && invocation.getStringDescriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;"))) { // J9+

                  // Ensure that these null checks are constant loads, LDC opcodes, null loads, bi/sipushes, or astores.
                  int nextOpc = seq.getInstr(i + 1).opcode;
                  if ((nextOpc >= opc_aconst_null && nextOpc <= opc_ldc2_w) || (nextOpc == opc_astore || (nextOpc >= opc_astore_0 && nextOpc <= opc_astore_3))) {
                    invocation.setSyntheticNullCheck();

                    // Objects.requireNonNull(qualifier); pop; <constant> is how javac reads an
                    // instance constant variable through a qualifying expression: the qualifier is
                    // null-checked, the value is inlined. The pushed constant is the field access.
                    if (nextOpc >= opc_aconst_null && nextOpc <= opc_ldc2_w) {
                      FieldExprent access = constantVariableAccess(invocation, exprlist, seq.getInstr(i + 1), pool, cl,
                        methodDescriptor, varProcessor.getMethod().hasModifier(CodeConstants.ACC_STATIC),
                        varProcessor, seq.getInstr(i + 1).startOffset);
                      if (access != null) {
                        // The check itself is not printed: javac re-emits it from the field access.
                        // Dropping the assignment here also keeps the qualified value's copy from
                        // resolving to the check's result, which shares its stack slot.
                        exprlist.remove(exprlist.size() - 1);
                        pendingFieldAccess = access;
                        pendingFieldIndex = i + 1;
                      }
                    }
                  }
                }
              }
            }
          }
          break;
        case opc_pop2:
          if (stack.getByOffset(-1).getExprType().stackSize == 1) {
            // Since value at the top of the stack is a value of category 1 (JVMS9 2.11.1)
            // we should remove one more item from the stack.
            // See JVMS9 pop2 chapter.
            stack.pop();
          }
          stack.pop();
          break;
      }
    }
  }

  /**
   * The value a {@code pop} discards when it can be the qualifier of a static member access
   * written through an expression, or null. Only a field access or a plain variable load
   * qualifies: javac evaluates such a qualifier and drops the value, while a discarded call is
   * an expression statement of its own and prints where it stands.
   */
  private static Exprent staticQualifierValue(List<Exprent> exprlist, ListStack<Exprent> stack) {
    if (exprlist.isEmpty() || stack.isEmpty()) {
      return null;
    }
    Exprent top = stack.getByOffset(-1);
    Exprent last = exprlist.get(exprlist.size() - 1);
    if (!(top instanceof VarExprent topVar) || !topVar.isStack()
        || !(last instanceof AssignmentExprent assign)
        || !(assign.getLeft() instanceof VarExprent target) || !target.isStack()
        || target.getIndex() != topVar.getIndex()) {
      return null;
    }
    Exprent value = assign.getRight();
    if (value instanceof FieldExprent) {
      return resolveStackVars(value, exprlist, exprlist.size() - 1, 0);
    }
    if (value instanceof VarExprent variable && !variable.isStack()) {
      return value.copy();
    }
    return null;
  }

  /**
   * A deep copy of a value with every stack temporary replaced by what it was assigned before it
   * was popped. The copy is printed inside a later exprent, where the stack simplifier would bind
   * the temporary to the last assignment at that depth instead of the one the pop discarded —
   * in {@code this.gameRenderer.preloadUiShader(x)} the same depth later holds the argument. Only
   * the assignments before {@code limit} may define a temporary: a getfield's result sits at the
   * same depth as its own receiver, so its own assignment would answer for the receiver.
   */
  private static Exprent resolveStackVars(Exprent value, List<Exprent> exprlist, int limit, int depth) {
    if (depth > 8) {
      return value.copy();
    }
    if (value instanceof VarExprent var && var.isStack()) {
      for (int i = Math.min(limit, exprlist.size()) - 1; i >= 0; i--) {
        if (exprlist.get(i) instanceof AssignmentExprent assign
            && assign.getLeft() instanceof VarExprent left && left.isStack()
            && left.getIndex() == var.getIndex()) {
          return resolveStackVars(assign.getRight(), exprlist, i, depth + 1);
        }
      }
      return value.copy();
    }
    if (value instanceof FieldExprent field) {
      FieldExprent copy = (FieldExprent) field.copy();
      if (field.getInstance() != null) {
        copy.setInstance(resolveStackVars(field.getInstance(), exprlist, limit, depth + 1));
      }
      return copy;
    }
    if (value instanceof InvocationExprent invocation) {
      InvocationExprent copy = (InvocationExprent) invocation.copy();
      if (invocation.getInstance() != null) {
        copy.setInstance(resolveStackVars(invocation.getInstance(), exprlist, limit, depth + 1));
      }
      List<Exprent> parameters = copy.getLstParameters();
      for (int i = 0; i < parameters.size(); i++) {
        parameters.set(i, resolveStackVars(parameters.get(i), exprlist, limit, depth + 1));
      }
      return copy;
    }
    return value.copy();
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent) {
    pushEx(stack, exprlist, exprent, null);
  }

  private void pushEx(ListStack<Exprent> stack, List<Exprent> exprlist, Exprent exprent, VarType vartype) {
    ValidationHelper.notNull(exprent);

    int varindex = VarExprent.STACK_BASE + stack.size();
    VarExprent var = new VarExprent(varindex, vartype == null ? exprent.getExprType() : vartype, varProcessor);
    var.setStack(true);

    exprlist.add(new AssignmentExprent(var, exprent, null));
    stack.push(var.copy());
  }

  private void insertByOffsetEx(int offset, ListStack<Exprent> stack, List<Exprent> exprlist, int copyoffset) {

    int base = VarExprent.STACK_BASE + stack.size();

    LinkedList<VarExprent> lst = new LinkedList<>();

    for (int i = -1; i >= offset; i--) {
      Exprent varex = stack.pop();
      VarExprent varnew = new VarExprent(base + i + 1, varex.getExprType(), varProcessor);
      varnew.setStack(true);
      exprlist.add(new AssignmentExprent(varnew, varex, null));
      lst.add(0, (VarExprent)varnew.copy());
    }

    Exprent exprent = lst.get(lst.size() + copyoffset).copy();
    VarExprent var = new VarExprent(base + offset, exprent.getExprType(), varProcessor);
    var.setStack(true);
    exprlist.add(new AssignmentExprent(var, exprent, null));
    lst.add(0, (VarExprent)var.copy());

    for (VarExprent expr : lst) {
      stack.push(expr);
    }
  }

  private static final int CONSTANT_EXACT = 0;
  private static final int CONSTANT_WIDENED = 1;
  private static final int CONSTANT_NO_MATCH = -1;

  /**
   * The field access a constant-variable read stands for, or {@code null} when the null check is
   * not one.
   *
   * <p>javac reads a constant variable through a qualifying expression by evaluating the
   * qualifier, null-checking it ({@code Objects.requireNonNull(qualifier)} + {@code pop}) and
   * pushing the inlined value. The class file records exactly that shape, and its position is the
   * evidence: a constant push right after such a check is the value of an instance constant field
   * of the qualifier's static type. The declaring class and field name are absent from the
   * constant pool (the access was inlined), so the field is chosen from the qualifier's type and
   * superclasses by value, with the same conversions javac applies when it pushes the constant.
   */
  private static FieldExprent constantVariableAccess(InvocationExprent invocation, List<Exprent> exprlist,
                                                     Instruction next, ConstantPool pool, StructClass cl,
                                                     MethodDescriptor methodDescriptor, boolean isStatic,
                                                     VarProcessor varProcessor, int offset) {
    if (!invocation.isStatic()
      || !invocation.getClassname().equals("java/util/Objects")
      || !invocation.getName().equals("requireNonNull")
      || invocation.getLstParameters().size() != 1) {
      return null;
    }

    if (!(invocation.getLstParameters().get(0) instanceof VarExprent argument)) {
      return null;
    }

    // The value the null check guarded is the most recent assignment to the same stack variable.
    // A parameter or local read directly into the check has no such assignment: the loaded
    // variable itself is the qualifier.
    Exprent qualifier = null;
    for (int i = exprlist.size() - 2; i >= 0; i--) {
      Exprent exprent = exprlist.get(i);
      if (exprent instanceof AssignmentExprent assignment
        && assignment.getLeft() instanceof VarExprent left
        && left.equalsVersions(argument)) {
        qualifier = assignment.getRight();
        break;
      }
    }
    if (qualifier == null && !argument.isStack() && argument.getLVT() != null) {
      qualifier = argument.copy();
    }
    if (qualifier == null) {
      return null;
    }

    ConstExprent pushed = pushedConstant(next, pool);
    if (pushed == null || pushed.getValue() == null) {
      return null;
    }

    VarType qualifierType = qualifier.getExprType();
    if (qualifier instanceof VarExprent qualifierVar) {
      // A parameter carries no LocalVariableTable entry at parse time (its entry starts at pc 0,
      // not after a load); the enclosing descriptor gives its declared type. A local that the
      // table does cover uses its entry. The parse-time stack type is only the category.
      VarType declared = qualifierVar.getLVT() != null ? qualifierVar.getLVT().getVarType()
        : parameterType(qualifierVar, cl, methodDescriptor, isStatic);
      if ((declared == null || declared.type != CodeType.OBJECT) && varProcessor.hasLVT()) {
        // Only the load that opens a variable's scope carries its table entry while the
        // expression list is built; a later load still has the entry whose range covers this pc.
        LocalVariable covering = null;
        List<LocalVariable> candidates =
          varProcessor.getCandidates(qualifierVar.getIndex());
        if (candidates != null) {
          for (LocalVariable candidate : candidates) {
            if (candidate.getStart() <= offset && offset < candidate.getEnd()
              && (covering == null || candidate.getStart() > covering.getStart())) {
              covering = candidate;
            }
          }
        }
        if (covering != null) {
          declared = covering.getVarType();
        }
      }
      if (declared != null && declared.type == CodeType.OBJECT && declared.arrayDim == 0) {
        qualifierType = declared;
      }
    }
    if (qualifierType.type != CodeType.OBJECT || qualifierType.arrayDim != 0) {
      return null;
    }

    StructClass owner = DecompilerContext.getStructContext().getClass(qualifierType.value);    if (owner == null) {
      return null;
    }

    FieldExprent exact = null;
    FieldExprent widened = null;
    Set<String> hidden = new HashSet<>();
    while (owner != null) {
      Set<String> declaredHere = new HashSet<>();
      for (StructField field : owner.getFields()) {
        if (hidden.contains(field.getName())) {
          continue; // a class on the path from the qualifier's type declares this name
        }
        declaredHere.add(field.getName());

        int access = field.getAccessFlags();
        if ((access & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) != CodeConstants.ACC_FINAL) {
          continue; // an instance constant variable is final and has no ConstantValue otherwise
        }
        StructConstantValueAttribute value = field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
        if (value == null) {
          continue;
        }
        PrimitiveConstant constant = owner.getPool().getPrimitiveConstant(value.getIndex());
        if (constant == null || constant.value == null || !accessibleFrom(cl, owner, access)) {
          continue;
        }

        int rank = constantMatch(field.getDescriptor(), constant.value, pushed.getConstType(), pushed.getValue());
        if (rank == CONSTANT_NO_MATCH) {
          continue;
        }

        // The field is read off the checked value itself, not off a copy of its expression: the
        // check's assignment is dropped, so this use resolves to the qualifier's own definition.
        FieldExprent candidate = new FieldExprent(field.getName(), owner.qualifiedName, false, argument.copy(),
          FieldDescriptor.parseDescriptor(field.getDescriptor()), null);
        if (rank == CONSTANT_EXACT) {
          if (exact == null) {
            exact = candidate;
          }
        }
        else if (widened == null) {
          widened = candidate;
        }
      }
      hidden.addAll(declaredHere);
      owner = owner.superClass == null ? null : DecompilerContext.getStructContext().getClass(owner.superClass.getString());
    }

    return exact != null ? exact : widened;
  }

  /** The declared type of a parameter slot in the method being decompiled. */
  private static VarType parameterType(VarExprent var, StructClass cl, MethodDescriptor descriptor, boolean isStatic) {
    int slot = var.getIndex();
    int position = 0;
    if (!isStatic) {
      if (slot == 0) {
        return new VarType("L" + cl.qualifiedName + ";");
      }
      position = 1;
    }
    for (VarType param : descriptor.params) {
      if (position == slot) {
        return param;
      }
      position += param.stackSize;
      if (position > slot) {
        return null;
      }
    }
    return null;
  }

  /** The pushed constant of a constant instruction, built as the main switch builds it. */
  private static ConstExprent pushedConstant(Instruction instr, ConstantPool pool) {
    switch (instr.opcode) {
      case opc_bipush:
      case opc_sipush:
        return new ConstExprent(instr.operand(0), true, null);
      case opc_lconst_0:
      case opc_lconst_1:
        return new ConstExprent(VarType.VARTYPE_LONG, (long)(instr.opcode - opc_lconst_0), null);
      case opc_fconst_0:
      case opc_fconst_1:
      case opc_fconst_2:
        return new ConstExprent(VarType.VARTYPE_FLOAT, (float)(instr.opcode - opc_fconst_0), null);
      case opc_dconst_0:
      case opc_dconst_1:
        return new ConstExprent(VarType.VARTYPE_DOUBLE, (double)(instr.opcode - opc_dconst_0), null);
      case opc_ldc:
      case opc_ldc_w:
      case opc_ldc2_w:
        PooledConstant constant = pool.getConstant(instr.operand(0));
        if (constant instanceof PrimitiveConstant) {
          return new ConstExprent(consts[constant.type - CONSTANT_Integer], ((PrimitiveConstant)constant).value, null);
        }
        return null;
      default:
        return null;
    }
  }

  /**
   * How a field's constant fits the pushed literal: exactly its declared type, or through a
   * conversion javac performs while pushing the constant (widening), which reproduces the same
   * pushed constant. Narrowing conversions are not implicit and never match.
   */
  private static int constantMatch(String descriptor, Object fieldValue, VarType pushedType, Object pushed) {
    if (pushedType.type == CodeType.BOOLEAN) {
      return descriptor.equals("Z") && fieldValue instanceof Integer flag && pushed instanceof Integer bit
        ? ((flag != 0) == (bit != 0) ? CONSTANT_EXACT : CONSTANT_NO_MATCH) : CONSTANT_NO_MATCH;
    }

    switch (descriptor) {
      case "I":
        if (!(fieldValue instanceof Integer number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Integer target) {
          return number.intValue() == target.intValue() ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Long target) {
          return number.longValue() == target ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number.floatValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "J":
        if (!(fieldValue instanceof Long number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Long target) {
          return number.longValue() == target ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number.floatValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "F":
        if (!(fieldValue instanceof Float number)) {
          return CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Float target) {
          return Float.compare(number, target) == 0 ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
        }
        if (pushed instanceof Double target) {
          return Double.compare(number.doubleValue(), target) == 0 ? CONSTANT_WIDENED : CONSTANT_NO_MATCH;
        }
        return CONSTANT_NO_MATCH;
      case "D":
        if (!(fieldValue instanceof Double number)) {
          return CONSTANT_NO_MATCH;
        }
        return pushed instanceof Double target && Double.compare(number, target) == 0 ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
      case "Ljava/lang/String;":
        return pushed instanceof String target && fieldValue instanceof String text && text.equals(target)
          ? CONSTANT_EXACT : CONSTANT_NO_MATCH;
      default:
        return CONSTANT_NO_MATCH;
    }
  }

  private static boolean accessibleFrom(StructClass current, StructClass owner, int access) {
    if ((access & CodeConstants.ACC_PUBLIC) != 0) {
      return true;
    }
    if ((access & CodeConstants.ACC_PRIVATE) != 0) {
      return nestHost(current).equals(nestHost(owner));
    }
    return packageOf(current.qualifiedName).equals(packageOf(owner.qualifiedName));
  }

  private static String nestHost(StructClass cls) {
    StructNestHostAttribute host = cls.getAttribute(StructGeneralAttribute.ATTRIBUTE_NEST_HOST);
    return host == null ? cls.qualifiedName : host.getHostClass(cls.getPool());
  }

  private static String packageOf(String internal) {
    int slash = internal.lastIndexOf('/');
    return slash < 0 ? "" : internal.substring(0, slash);
  }

  public static boolean canonicalizeCasts(RootStatement stat) {
    boolean res = false;
    while (canonicalizeCasts((Statement) stat)) {
      res = true;
    }

    return res;
  }

  private static boolean canonicalizeCasts(Statement stat) {
    boolean res = false;
    for (Statement st : stat.getStats()) {
      res |= canonicalizeCasts(st);
    }

    if (stat instanceof BasicBlockStatement) {
      for (Exprent exprent : stat.getExprents()) {
        for (Exprent ex : exprent.getAllExprents(true, true)) {

          // Remove Checkcast(Type, Checkcast(Type, ...)) and turn it just into Checkcast(Type, ...) where both have the same type
          // The extra checkcast causes issues with generic type decompilation
          if (ex instanceof FunctionExprent && ((FunctionExprent)ex).getFuncType() == FunctionExprent.FunctionType.CAST) {
            FunctionExprent func = (FunctionExprent)ex;
            Exprent inner = func.getLstOperands().get(0);
            Exprent cast = func.getLstOperands().get(1);

            if (inner instanceof FunctionExprent && ((FunctionExprent)inner).getFuncType() == FunctionExprent.FunctionType.CAST) {
              FunctionExprent func2 = (FunctionExprent)inner;
              Exprent inner2 = func2.getLstOperands().get(0);
              Exprent cast2 = func2.getLstOperands().get(1);

              if (cast.getExprType().equals(cast2.getExprType())) {
                ex.replaceExprent(inner, inner2);
                ex.addBytecodeOffsets(inner2.bytecode);
                ex.addBytecodeOffsets(inner.bytecode);
                res = true;
              }
            }
          }
        }
      }
    }

    return res;
  }

  public static void markExprOddities(RootStatement root) {
    // We shouldn't have to do this, but turns out getting cast names is not pure. Sigh.
    try (var lock = DecompilerContext.getImportCollector().lock()) {
      markExprOddities(root, root);
    }
  }

  private static void markExprOddities(RootStatement root, Statement stat) {
    for (Statement st : stat.getStats()) {
      markExprOddities(root, st);
    }

    for (Exprent ex : stat.getVarDefinitions()) {
      markExprOddity(root, ex, true);
    }

    if (stat instanceof BasicBlockStatement) {
      if (stat.isLabeled()) {
        root.addComment("$VF: Made invalid labels!", true);
      }

      for (Exprent ex : stat.getExprents()) {
        markExprOddity(root, ex, true);
      }
    }

    if (stat instanceof IfStatement ifSt) {
      markExprOddity(root, ifSt.getHeadexprent(), false);
    }
  }

  private static void markExprOddity(RootStatement root, Exprent ex, boolean block) {
    if (ex instanceof MonitorExprent) {
      root.addComment("$VF: Could not create synchronized statement, marking monitor enters and exits", true);
    }
    if (block && ex instanceof IfExprent) {
      root.addComment("$VF: Accidentally destroyed if statement, the decompiled code is not correct!", true);
    }

    ClassWrapper wrapper = AssertProcessor.getHoldingClass();
    MethodProperties prop = wrapper.getMethodProperties("<clinit>", "()V");

    for (Exprent e : ex.getAllExprents(true, true)) {
      if (e instanceof VarExprent) {
        VarExprent var = (VarExprent)e;
        if (var.isDefinition() && isInvalidTypeName(var.getDefinitionType()) || var.getExprType() == VarType.VARTYPE_UNKNOWN) {
          root.addComment("$VF: Could not properly define all variable types!", true);
        }
      } else if (e instanceof FunctionExprent) {
        FunctionExprent func = (FunctionExprent)e;
        if (func.getFuncType() == FunctionType.CAST && func.doesCast()) {
          List<Exprent> operands = func.getLstOperands();
          if (isInvalidTypeName(operands.get(1).toString())) {
            root.addComment("$VF: Could not properly define all variable types!", true);
          }
        }
      } else if (e instanceof FieldExprent field) {
        if (prop != null && prop.assertField != null && root.mt != prop.mt) {
          if (field.getName().equals(prop.assertField.getName()) && field.getClassname().equals(wrapper.getClassStruct().qualifiedName)) {
            root.addComment("$VF: Could not resugar all assert statements!", true);
          }
        }
      }
    }
  }

  public static String getTypeName(VarType type) {
    return getTypeName(type, true);
  }

  public static String getTypeName(VarType type, boolean getShort) {
    CodeType tp = type.type;
    if (tp.ordinal() <= CodeType.BOOLEAN.ordinal()) {
      return typeNames[tp.ordinal()];
    }
    else if (tp == CodeType.UNKNOWN) {
      return UNKNOWN_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.NULL) {
      return NULL_TYPE_STRING; // INFO: should not occur
    }
    else if (tp == CodeType.VOID) {
      return "void";
    }
    else if (tp == CodeType.GENVAR && type.isGeneric()) {
      return type.value;
    }
    else if (tp == CodeType.OBJECT) {
      if (type.isGeneric()) {
        return ((GenericType)type).getCastName();
      }
      String ret = buildJavaClassName(type.value);
      if (getShort) {
        ret = DecompilerContext.getImportCollector().getShortName(ret);
      }

      if (ret == null) {
        ret = UNDEFINED_TYPE_STRING;
      }
      return ret;
    }

    // Unrepresentable: only for debugging
    if (tp == CodeType.BYTECHAR) {
      return "<bytechar>";
    }

    if (tp == CodeType.SHORTCHAR) {
      return "<shortchar>";
    }

    throw new RuntimeException("invalid type: " + tp);
  }

  public static boolean isInvalidTypeName(String name) {
    return UNDEFINED_TYPE_STRING.equals(name) || NULL_TYPE_STRING.equals(name) || UNKNOWN_TYPE_STRING.equals(name);
  }

  public static String getCastTypeName(VarType type) {
    return getCastTypeName(type, true);
  }

  public static String getCastTypeName(VarType type, boolean getShort) {
    StringBuilder s = new StringBuilder(getTypeName(type, getShort));
    TextUtil.append(s, "[]", type.arrayDim);
    return s.toString();
  }

  public static PrimitiveExprsList getExpressionData(VarExprent var) {
    PrimitiveExprsList prlst = new PrimitiveExprsList();
    VarExprent vartmp = new VarExprent(VarExprent.STACK_BASE, var.getExprType(), var.getProcessor());
    vartmp.setStack(true);

    VarExprent catchVar = (VarExprent) var.copy();
    catchVar.setCatchTempVar(true);
    prlst.getLstExprents().add(new AssignmentExprent(vartmp, catchVar, null));
    prlst.getStack().push(vartmp.copy());
    return prlst;
  }

  public static boolean endsWithSemicolon(Exprent expr) {
    return !(expr instanceof SwitchHeadExprent ||
             expr instanceof MonitorExprent ||
             expr instanceof IfExprent ||
             (expr instanceof VarExprent && ((VarExprent)expr).isClassDef()));
  }

  public static int addDeletedGotoInstructionMapping(Statement stat, TextBuffer buffer) {
    if (stat instanceof BasicBlockStatement) {
      BasicBlock block = ((BasicBlockStatement)stat).getBlock();
      List<Integer> offsets = block.getInstrOldOffsets();
      if (!offsets.isEmpty() &&
          offsets.size() > block.getSeq().length()) { // some instructions have been deleted, but we still have offsets
        int last = offsets.get(offsets.size() - 1);
        buffer.addBytecodeMapping(last); // add the last offset
        return last;
      }
    }
    return -1;
  }

  /** The block already left through a switch-expression yield; a jump print would be dead. */
  private static boolean yieldsFromBlock(Statement stat) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent instanceof YieldExprent) {
          return true;
        }
      }
    }
    return false;
  }

  public static TextBuffer jmpWrapper(Statement stat, int indent, boolean semicolon) {
    return jmpWrapper(stat, indent, semicolon, -1);
  }

  /**
   * Prints the statement, then the jump its out-edge stands for, mapping the jump's bytecode
   * offset onto the printed keyword.
   *
   * <p>{@code fallbackJump} is the offset of the jump the printed {@code break;}/{@code continue;}
   * compiles to when the statement itself no longer records it: an empty block has no deleted
   * instruction to read, and a non-block statement never had its offsets harvested. The switch
   * that owns the arm knows the jump's offset from the table, and without the mapping the
   * alignment cannot tell the jump's line from the next statement's.
   */
  public static TextBuffer jmpWrapper(Statement stat, int indent, boolean semicolon, int fallbackJump) {
    if (RoundTrip.isDeferredExit(stat)) {
      // The loop prints this block after its closing brace; here the source jumped to it.
      TextBuffer jump = new TextBuffer();
      if (stat instanceof org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement ifstat
          && ifstat.getFirst() != null) {
        // A head block the if merged before the tail ran where it stands; only what follows moves.
        jump.append(ifstat.getFirst().toJava(indent));
        RoundTrip.consumeHead(stat);
      }
      jump.appendIndent(indent);
      // The keyword is the jump the source wrote to reach the block. Without the mapping the
      // aligner has no line for it and pays the gap in front of the block after the loop.
      int site = RoundTrip.deferredExitJumpSite(stat);
      if (site >= 0) {
        jump.addBytecodeMapping(site);
      }
      jump.append("break;").appendLineSeparator();
      return jump;
    }
    TextBuffer buf = stat.toJava(indent);

    List<StatEdge> lstSuccs = stat.getSuccessorEdges(Statement.STATEDGE_DIRECT_ALL);
    if (lstSuccs.size() == 1) {
      StatEdge edge = lstSuccs.get(0);
      if (edge.getType() != StatEdge.TYPE_REGULAR && edge.explicit && !(edge.getDestination() instanceof DummyExitStatement)
        && !yieldsFromBlock(stat) && !RoundTrip.isJumpSuppressed(stat) && !RoundTrip.isClosureHidden(edge)
        && !RoundTrip.printedBreak(stat) && !RoundTrip.isDeferredBreak(edge)
        // The edge is the loop's own back edge: the target's branch lands on a goto to the head,
        // so the source wrote no continue and the branch falls into the latch instead. A labelled
        // continue is a source statement of its own and keeps its printed jump.
        && !(edge.getType() == StatEdge.TYPE_CONTINUE && !edge.labeled
             && RoundTrip.landsOnLoopLatch(stat))) {
        int jumpOffset = addDeletedGotoInstructionMapping(stat, buf);
        if (jumpOffset < 0 && fallbackJump >= 0) {
          // The statement no longer carries the deleted jump's offset; the arm's owner knows it.
          // Only the mapping is taken from it: the keyword's kind and its line are decided by the
          // tree's own evidence, and an offset this block never had must not change them.
          buf.addBytecodeMapping(fallbackJump);
        } else if (jumpOffset < 0) {
          // Neither the block nor its owner records the jump: the outgoing edge itself still
          // names it, as the unique goto between this statement's last instruction and the
          // edge's destination that lands exactly there. Without the mapping the keyword's line
          // is left to the aligner's guess and can land two lines off.
          int site = RoundTrip.outgoingJumpSite(stat, edge);
          if (site >= 0) {
            buf.addBytecodeMapping(site);
          }
        }
        // The target starts no line at the jump when the source ended the previous statement with
        // `break;`/`continue;` on the same line; keep it there.
        boolean join = jumpOffset >= 0 && !RoundTrip.lineStartsAt(jumpOffset)
          && buf.length() >= DecompilerContext.getNewLineSeparator().length();
        if (join) {
          buf.setLength(buf.length() - DecompilerContext.getNewLineSeparator().length());
          buf.append(" ");
        } else {
          buf.appendIndent(indent);
        }

        // A labelled continue whose jump lands on an enclosing loop's own end through another
        // goto is the source's `break label;` of that loop: the named outer continue compiles to
        // the head jump directly, with no trampoline in between.
        Statement trampolineBreak = edge.getType() == StatEdge.TYPE_CONTINUE
          ? RoundTrip.trampolineBreakLoop(edge, stat, jumpOffset) : null;
        if (trampolineBreak != null && !RoundTrip.printsLabel(trampolineBreak)) {
          // The loop would print no label of its own; the plain continue is the safe form.
          trampolineBreak = null;
        }
        if (trampolineBreak != null) {
          buf.append("break label").append(trampolineBreak.id);
        } else {
          switch (edge.getType()) {
            case StatEdge.TYPE_BREAK:
              // A break out of the loop body's last switch and a continue compile to different
              // jumps; the target's jump at this offset says which one the source wrote.
              boolean continues = !edge.labeled
                && (RoundTrip.breakJumpsToContinue(jumpOffset) || RoundTrip.emptyArmContinues(stat))
                && !RoundTrip.armBreakAtLoopLatch(stat, jumpOffset);
              buf.append(continues ? "continue" : "break");
              break;
            case StatEdge.TYPE_CONTINUE:
              // An arm's jump that lands on the loop's bare back-edge goto is the switch's break:
              // a written continue would reach the loop's continue target with no goto between.
              boolean latchBreak = !edge.labeled && RoundTrip.armBreakAtLoopLatch(stat, jumpOffset);
              buf.append(latchBreak ? "break" : "continue");
          }

          boolean needsName = edge.labeled || RoundTrip.leavesClosure(edge);
          if (needsName) {
            buf.append(" label").append(edge.closure.id);
          }
        }
        buf.append(";").appendLineSeparator();
      }
    }

    if (buf.length() == 0 && semicolon) {
      buf.appendIndent(indent).append(";").appendLineSeparator();
    }

    return buf;
  }

  public static String buildJavaClassName(String name) {
    String res = name.replace('/', '.');

    if (res.contains("$")) { // attempt to invoke foreign member
      // classes correctly
      StructClass cl = DecompilerContext.getStructContext().getClass(name);
      if (cl == null || !cl.isOwn()) {
        res = res.replace('$', '.');
      }
    }

    return res;
  }

  public static TextBuffer listToJava(List<? extends Exprent> lst, int indent) {
    if (lst == null || lst.isEmpty()) {
      return new TextBuffer();
    }

    StructClass cl = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
    LanguageSpec spec = PluginContext.getCurrentContext().getLanguageSpec(cl);

    TextBuffer buf = new TextBuffer();
    lst = Exprent.sortIndexed(lst);

    for (Exprent expr : lst) {
      // The form being printed already stands for this exit (a compact record constructor's
      // implicit return); printing the exprent would add a statement the source does not have.
      if (RoundTrip.isConsumedExit(expr)) {
        continue;
      }
      if (buf.length() > 0 && expr instanceof VarExprent && ((VarExprent)expr).isClassDef()) {
        // separates local class definition from previous statements
        buf.appendLineSeparator();
      }

      expr.getInferredExprType(null);

      TextBuffer content = expr.toJava(indent);

      if (content.length() > 0) {
        // The statement's text begins with the loads feeding its first instruction, and the
        // expression maps only the instruction it owns: without a mapping at the leaf the aligner
        // cannot see the line the table puts the statement's start on. The leaf is the walked-back
        // load, not necessarily the exprent's first own offset, because an align-only mapping
        // there would overwrite a plain one.
        int leaf = RoundTrip.operandStartOffset(expr);
        if (leaf >= 0 && RoundTrip.lineStartsAt(leaf)) {
          content.addStartBytecodeMapping(leaf);
        }
        if (!(expr instanceof VarExprent) || !((VarExprent)expr).isClassDef()) {
          buf.appendIndent(indent);
        }
        buf.append(content);
        if (expr instanceof MonitorExprent && ((MonitorExprent)expr).getMonType() == MonitorExprent.Type.ENTER) {
          buf.append("{} // $VF: monitorenter "); // empty synchronized block
        }
        if (spec != null) {
          if (spec.writer.endsWithSemicolon(expr)) {
            buf.append(';');
          }
        } else {
          if (endsWithSemicolon(expr)) {
            buf.append(';');
          }
        }
        buf.appendLineSeparator();
      }
    }

    return buf;
  }

  public static ConstExprent getDefaultArrayValue(VarType arrType) {
    ConstExprent defaultVal;
    if (arrType.type == CodeType.OBJECT || arrType.arrayDim > 0) {
      defaultVal = new ConstExprent(VarType.VARTYPE_NULL, null, null);
    }
    else if (arrType.type == CodeType.FLOAT) {
      defaultVal = new ConstExprent(VarType.VARTYPE_FLOAT, 0f, null);
    }
    else if (arrType.type == CodeType.LONG) {
      defaultVal = new ConstExprent(VarType.VARTYPE_LONG, 0L, null);
    }
    else if (arrType.type == CodeType.DOUBLE) {
      defaultVal = new ConstExprent(VarType.VARTYPE_DOUBLE, 0d, null);
    }
    else { // integer types
      defaultVal = new ConstExprent(0, true, null);
    }
    return defaultVal;
  }

  /**
   * The cast-expression type annotations the target records on this expression's own cast.
   *
   * <p>A cast whose type erases to the operand's own type emits no {@code checkcast}; javac still
   * records the cast expression's type annotation with the offset of the first instruction after
   * the operand. The expression the printer wraps in that cast ends exactly there, so an
   * annotation whose offset equals the end of this expression's last instruction was written on
   * this cast. Only a top-level path applies to the cast type itself.
   */
  private static List<org.jetbrains.java.decompiler.util.Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> castAnnotations(
    Exprent exprent) {
    StructMethod method = RoundTrip.currentMethod();
    if (method == null || exprent.bytecode == null || exprent.bytecode.isEmpty()) {
      return Collections.emptyList();
    }
    // The exprent's mapping may record a point past the last instruction it emits (an argument's
    // end, a dropped marker); the cast's offset is the end of the last real instruction.
    int end = -1;
    for (int bit = exprent.bytecode.nextSetBit(0); bit >= 0;
         bit = exprent.bytecode.nextSetBit(bit + 1)) {
      end = Math.max(end, RoundTrip.instructionEnd(method, bit));
    }
    if (end < 0) {
      return Collections.emptyList();
    }
    List<org.jetbrains.java.decompiler.util.Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> list = null;
    for (org.jetbrains.java.decompiler.util.Key<?> key : org.jetbrains.java.decompiler.main.ClassWriter.TYPE_ANNOTATION_ATTRIBUTES) {
      org.jetbrains.java.decompiler.struct.attr.StructTypeAnnotationAttribute attribute =
        method.getAttribute((org.jetbrains.java.decompiler.util.Key<org.jetbrains.java.decompiler.struct.attr.StructTypeAnnotationAttribute>)key);
      if (attribute == null) {
        continue;
      }
      for (TypeAnnotation annotation : attribute.getAnnotations()) {
        if (annotation.getTargetType() != TypeAnnotation.TYPE_ARG_CAST
          || annotation.getIndex() != end || !annotation.isTopLevel()) {
          continue;
        }
        if (list == null) {
          list = new ArrayList<>();
        }
        list.add(org.jetbrains.java.decompiler.util.Pair.of(annotation.asQueue(),
          annotation.getAnnotation()));
      }
    }
    return list == null ? Collections.emptyList() : list;
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         boolean castNull) {
    return getCastedExprent(exprent, leftType, buffer, indent, castNull ? NullCastType.CAST : NullCastType.DONT_CAST, false, false, false);
  }

  private static boolean isPrimitive(VarType type) {
    if (type == null) {
      return false;
    }
    return switch (type.type) {
      case BOOLEAN, BYTE, CHAR, SHORT, INT, LONG, FLOAT, DOUBLE -> true;
      default -> false;
    };
  }

  /** Whether the table records this variable's own type at {@code type}. */
  private static boolean recordedPrimitiveMatches(Exprent exprent, VarType type) {
    if (!(exprent instanceof VarExprent var) || var.getLVT() == null) {
      return false;
    }
    VarType recorded = var.getLVT().getVarType();
    return recorded != null && isPrimitive(recorded) && recorded.equals(type);
  }

  /** The type the local variable table records for this variable, signature first. */
  public static @Nullable VarType recordedVarType(VarExprent var) {
    LocalVariable lvt = var.getLVT();
    if (lvt == null && var.getProcessor() != null) {
      lvt = var.getProcessor().getVarLVT(var.getVarVersionPair());
    }
    if (lvt == null && var.getProcessor() != null && var.getProcessor().hasLVT()) {
      // The version-keyed map does not hold every slot: a parameter's row starts at pc 0, and
      // the use's own VarExprent is a different version pair. The table's range query answers
      // for the value's instruction, and the innermost row is the variable visible there.
      Integer slot = var.getProcessor().getVarOriginalIndex(var.getIndex());
      int offset = var.bytecode == null || var.bytecode.isEmpty() ? -1 : var.bytecode.nextSetBit(0);
      if (slot != null && offset >= 0) {
        lvt = var.getProcessor().getMethod().getLocalVariableAttr()
          .matchingVars(slot, offset)
          .max(Comparator.comparingInt(LocalVariable::getStartPC))
          .orElse(null);
      }
    }
    if (lvt == null) {
      return null;
    }
    if (lvt.getSignature() != null) {
      try {
        return GenericType.parse(lvt.getSignature());
      } catch (RuntimeException ignored) {
        return lvt.getVarType();
      }
    }
    return lvt.getVarType();
  }

  /** Exact type equality, including generic arguments and wildcards. */
  private static boolean sameType(VarType left, VarType right) {
    if (left == right) {
      return true;
    }
    if (left == null || right == null) {
      return false;
    }
    if (left instanceof GenericType generic) {
      return generic.equalsExact(right);
    }
    if (right instanceof GenericType generic) {
      return generic.equalsExact(left);
    }
    return left.equals(right);
  }

  /**
   * Whether the expression is a generic call whose own type variable appears only in the return
   * type and whose inferred type is exactly that variable's erasure (or its array). No argument
   * constrains such a variable, so javac infers it from the context target alone; a source that
   * compiled passed the call bare into that target. A variable that also sits in a parameter
   * (Arrays.copyOf's {@code Class<? extends T[]>}) is inferred from the argument and excluded.
   */
  private static boolean targetTypedFreeReturn(Exprent exprent, VarType rightType) {
    if (!(exprent instanceof InvocationExprent call) || rightType == null) {
      return false;
    }
    StructMethod method = call.getDesc();
    GenericMethodDescriptor signature = method == null ? null : method.getSignature();
    if (signature == null || signature.typeParameters.isEmpty()) {
      return false;
    }
    VarType declaredReturn = signature.returnType;
    if (!(declaredReturn instanceof GenericType returnGeneric) || returnGeneric.type != CodeType.GENVAR
      || returnGeneric.getWildcard() != GenericType.WILDCARD_NO || returnGeneric.value == null
      || !signature.typeParameters.contains(returnGeneric.value)) {
      return false;
    }
    for (VarType parameter : signature.parameterTypes) {
      if (mentionsTypeVariable(parameter, returnGeneric.value)) {
        return false;
      }
    }
    int index = signature.typeParameters.indexOf(returnGeneric.value);
    VarType bound = index < signature.typeParameterBounds.size()
      && !signature.typeParameterBounds.get(index).isEmpty()
      ? signature.typeParameterBounds.get(index).get(0) : VarType.VARTYPE_OBJECT;
    VarType erasedBase = erasedBound(bound);
    if (erasedBase == null || erasedBase.value == null) {
      return false;
    }
    VarType erasedReturn = new VarType(erasedBase.type, erasedBase.arrayDim + returnGeneric.arrayDim, erasedBase.value);
    return sameErasedType(rightType, erasedReturn);
  }

  /** The erasure of a declared bound: its class without type arguments. */
  private static @Nullable VarType erasedBound(VarType bound) {
    if (bound == null) {
      return VarType.VARTYPE_OBJECT;
    }
    if (bound.type == CodeType.GENVAR) {
      // A bound naming another variable erases to that variable's own bound; Object is the safe
      // stand-in because a match only ever widens to the target.
      return VarType.VARTYPE_OBJECT;
    }
    return new VarType(bound.type, bound.arrayDim, bound.value);
  }

  /** Equality of the erasure: type and array dimension, ignoring generic arguments. */
  private static boolean sameErasedType(VarType value, VarType expected) {
    return value != null && expected != null
      && value.type == expected.type && value.arrayDim == expected.arrayDim
      && value.value != null && value.value.equals(expected.value);
  }

  /**
   * Whether two instantiations of the same invariant generic class disagree at an argument
   * position. Two different types never assign across an invariant position, so a source that
   * compiled converted the value; a wildcard or a capture at a differing position is not that
   * kind of difference (the source may have written the wildcard to widen the value), so only a
   * position whose two sides are nameable types that differ counts.
   */
  public static boolean invariantInstantiationsDiffer(VarType parameter, VarType value) {
    if (!(parameter instanceof GenericType parameterType) || !(value instanceof GenericType valueType)
      || parameterType.getWildcard() != GenericType.WILDCARD_NO
      || valueType.getWildcard() != GenericType.WILDCARD_NO
      || parameter.type != CodeType.OBJECT || value.type != CodeType.OBJECT
      || parameter.arrayDim != 0 || value.arrayDim != 0
      || parameter.value == null || !parameter.value.equals(value.value)) {
      return false;
    }
    List<VarType> parameterArguments = parameterType.getArguments();
    List<VarType> valueArguments = valueType.getArguments();
    if (parameterArguments.size() != valueArguments.size()) {
      return false;
    }
    boolean differs = false;
    for (int i = 0; i < parameterArguments.size(); i++) {
      VarType left = parameterArguments.get(i);
      VarType right = valueArguments.get(i);
      if (sameType(left, right)) {
        continue;
      }
      if (isWildcardArgument(left) || isWildcardArgument(right)
        || hasWildcard(left) || hasWildcard(right)) {
        return false;
      }
      differs = true;
    }
    return differs;
  }

  public static boolean getCastedExprent(Exprent exprent,
                                         VarType leftType,
                                         TextBuffer buffer,
                                         int indent,
                                         NullCastType castNull,
                                         boolean castAlways,
                                         boolean castNarrowing,
                                         boolean unbox) {

    if (unbox) {
      // "unbox" invocation parameters, e.g. 'byteSet.add((byte)123)' or 'new ShortContainer((short)813)'
      if (exprent instanceof InvocationExprent) {
        InvocationExprent invocationExprent = (InvocationExprent) exprent;
        if (invocationExprent.isBoxingCall() && !invocationExprent.shouldForceBoxing()) {
          exprent = invocationExprent.getLstParameters().get(0);
          CodeType paramType = invocationExprent.getDescriptor().params[0].type;
          if (exprent instanceof ConstExprent && ((ConstExprent) exprent).getConstType().type != paramType) {
            leftType = new VarType(paramType);
          }
        }
      }
    }

    VarType rightType;
    // A lambda parameter is typed by its functional target only where the target's type is
    // exactly the context's: otherwise the source's own conversion (often a cast that pins a
    // generic inference) is what the body wrote, and the parameter's own inference must decide.
    if (exprent instanceof VarExprent lambdaVar && lambdaVar.hasLambdaParameterType()
        && !lambdaVar.lambdaParameterTypeEquals(leftType)) {
      Exprent.suspendLambdaParameterTypes();
      try {
        rightType = exprent.getInferredExprType(leftType);
      } finally {
        Exprent.resumeLambdaParameterTypes();
      }
    } else {
      rightType = exprent.getInferredExprType(leftType);
    }
    // A lambda's own parameter is implicitly typed by the non-wildcard parameterization of its
    // functional target: a wildcard in an input position stands for its bound. Only where that
    // bound is the very class the context expects is the recorded wildcard the target's
    // spelling of this value; elsewhere it is the range that selects the cast guiding the
    // enclosing inference, and the recorded form stays.
    if (InvocationExprent.inArgument()
        && exprent instanceof VarExprent lambdaVar && lambdaVar.hasLambdaParameterType()
        && rightType instanceof GenericType wildcardRight
        && wildcardRight.getWildcard() != GenericType.WILDCARD_NO
        && wildcardRight.value != null
        && leftType != null && leftType.type == CodeType.OBJECT
        && wildcardRight.value.equals(leftType.value)) {
      rightType = GenericType.withWildcard(wildcardRight, GenericType.WILDCARD_NO);
    }
    // A local whose table row records exactly the target type needs no cast: the printer's own
    // inference fell back to an erasure or a wildcard the source never wrote.
    if (exprent instanceof VarExprent recordedVar) {
      VarType recorded = recordedVarType(recordedVar);
      if (recorded != null && sameType(recorded, leftType)) {
        rightType = leftType;
      }
    }
    // A generic call whose own type variable appears only in its return type has no argument to
    // infer it from: javac types that variable from the context target alone. When the printer's
    // inference left the variable at its erasure, every cast to the target is the printer's;
    // passing the call bare is the form the source wrote, and javac re-infers the variable from
    // the target.
    if (leftType != null && targetTypedFreeReturn(exprent, rightType)) {
      rightType = leftType;
    }
    // The inference just dropped a target mapping this call's own functional argument types from
    // its body (a chain on a wildcard receiver): the target did not type the call, and the
    // source cast its result.
    boolean functionalBodyTargetDropped = exprent instanceof InvocationExprent openCall
      && openCall.droppedTargetVariable();
    // A switch expression's target is handed to the arms only when no outer cast is printed:
    // then the switch is poly in this context and the arms are printed against this target.
    exprent = narrowGenericCastType(exprent, leftType);

    // A cast around a context-independent value whose recorded type is exactly the context
    // target converts nothing: javac sees the operand at the target type and reports the cast
    // redundant. A local's own table row is the type its declaration gives it, so that equality
    // holds in an argument list too; a field's inferred type can echo an inference variable the
    // printer solved from the value itself, so its equality counts only elsewhere. Poly
    // expressions are excluded — the target is what types them — and so is an overload-choice
    // cast. Constants are excluded too: their inferred type is the context's, and a narrowing
    // constant cast is what makes a byte/short argument or constructor compile.
    // A lambda parameter's recorded type can keep the functional target's wildcard form; the
    // value's own source type is its bound (`? super X` stands for X there), so the variable is
    // exactly the target when the bound is.
    boolean wildcardParameter = exprent instanceof VarExprent
      && rightType instanceof GenericType wildcardRight
      && wildcardRight.getWildcard() != GenericType.WILDCARD_NO
      && sameType(GenericType.withWildcard(wildcardRight, GenericType.WILDCARD_NO), leftType);

    boolean exactRecordedType = !castAlways && rightType != null
      && ((exprent instanceof VarExprent recordedVar && sameType(recordedVarType(recordedVar), leftType))
          || (exprent instanceof VarExprent lambdaVar && lambdaVar.lambdaParameterTypeEquals(leftType))
          || wildcardParameter
          || (!InvocationExprent.inArgument()
              && (exprent instanceof VarExprent || exprent instanceof FieldExprent)
              && sameType(rightType, leftType))
          // A field whose recorded Signature is exactly the context target converts nothing,
          // whatever the context: the source's cast was redundant and javac reports it. The
          // qualifier must itself be context-independent, since a call chain's type can take
          // its arguments from the target and change what the field access means.
          || (exprent instanceof FieldExprent recordedField
              && contextIndependentQualifier(recordedField)
              && !(InvocationExprent.inArgument() && InvocationExprent.argumentTargetMayInfer())
              && sameType(recordedField.getInferredExprType(null), leftType)));

    boolean doCast = (!leftType.higherEqualInLatticeThan(rightType) && (rightType.equals(VarType.VARTYPE_OBJECT) || leftType.type != CodeType.OBJECT));
    // A switch expression is poly: with a type variable as the target, javac infers the switch's
    // own type from that target and casts each arm to the erasure, leaving no cast after the
    // merge. Our switch type came out as the bare erasure, so the outer cast is the printer's.
    boolean doCastNull = (castNull.cast && rightType.type == CodeType.NULL && !UNDEFINED_TYPE_STRING.equals(getTypeName(leftType)));
    boolean doCastNarrowing = (castNarrowing && isIntConstant(exprent) && isNarrowedIntType(leftType));
    boolean doCastGenerics = doGenericTypesCast(exprent, leftType, rightType);
    // An instance call's return type carries the receiver class's type variable, which the
    // target cannot re-infer: an invariant argument mismatch between them is a conversion only
    // the source's cast performs. javac emits no instruction for the cast because the erasures
    // already match.
    if (!doCastGenerics && exprent instanceof InvocationExprent call
      && call.getInstance() != null && !call.isStatic() && !call.isPolyCall()
      && invariantTypeVariableMismatch(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }
    // A generic array creation can only name its component through the all-wildcard form
    // `new X<?>[]`; when the recorded target instantiates that same component with type
    // arguments, the wildcard array is not assignable to it (arrays are invariant over
    // non-reifiable components) and the source cast the creation.
    if (!doCastGenerics && exprent instanceof NewExprent creation
      && creation.printsWildcardArrayComponentFor(leftType)
      && rightType instanceof GenericType value && value.type == CodeType.OBJECT
      && value.value != null && value.value.equals(leftType.value)
      && value.arrayDim == leftType.arrayDim && !sameType(leftType, rightType)) {
      doCastGenerics = true;
    }
    // The same conversion through an array-constructor argument: when the call's target
    // component is not reifiable, the lambda prints `X<?>[]::new` and the call returns the
    // wildcard array, which is not assignable to the recorded target (arrays are invariant
    // over non-reifiable components). The source cast the call's result.
    InvocationExprent arrayConstructorCall = null;
    if (exprent instanceof InvocationExprent directCall) {
      arrayConstructorCall = directCall;
    } else if (exprent instanceof FunctionExprent castWrapper
      && castWrapper.getFuncType() == FunctionType.CAST
      && !castWrapper.getLstOperands().isEmpty()
      && castWrapper.getLstOperands().get(0) instanceof InvocationExprent wrappedCall) {
      arrayConstructorCall = wrappedCall;
    }
    if (!doCastGenerics && arrayConstructorCall != null) {
      for (Exprent parameter : arrayConstructorCall.getLstParameters()) {
        if (parameter instanceof NewExprent arrayConstructor
          && arrayConstructor.printsWildcardArrayConstructorFor(leftType)) {
          doCastGenerics = true;
          break;
        }
      }
    }
    // Inference substituted the upper bound into the call's type, so the wildcard the method
    // declared has vanished; the original source had to cast that capture away, and javac elides
    // the checkcast because the erasures match.
    if (!doCastGenerics
        && exprent instanceof InvocationExprent invocation
        && needsCaptureCast(leftType, invocation.getDeclaredGenericReturnType())) {
      doCastGenerics = true;
    }
    // A target whose wildcard is a lower bound over a type variable of this scope (`? super S`)
    // accepts no captured argument: javac cannot prove the value's capture is a supertype of S,
    // whatever the value's own class is. The source cast the value to the declared target, and
    // javac elides that checkcast when the erasures already match.
    // A poly call is the exception: its own type parameters are what the target instantiates,
    // and javac infers them from that target again, so the source let the context solve it.
    if (!doCastGenerics && !doCast && exprent instanceof InvocationExprent invocation
        && !invocation.isPolyCall()
        && lowerBoundedWildcardTarget(leftType) && castableToErasure(exprent, leftType)) {
      doCastGenerics = true;
    }
    // A cast whose own type arguments violate the target's bounds cannot appear in a source that
    // compiled. The inference that produced it is wrong; passing the expression on lets javac infer
    // again, which is what the original source did.
    if (doCastGenerics && !doCast && invalidGenericInstantiation(leftType)) {
      doCastGenerics = false;
    }
    // A target whose direct type argument is a type variable in scope, against a value whose same
    // position is a wildcard: a wildcard is never literally the variable, so the value does not
    // assign across an invariant position and the source cast it. Only this direction casts
    // (X<T> is an X<?>), only a value whose type the class file fixes without context is cast,
    // and an out-of-scope variable cannot be named in the cast.
    if (!doCastGenerics
      && contextIndependentValue(exprent)
      && invariantWildcardTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }
    // The same mismatch one level up the hierarchy: the value's recorded type instantiates a
    // subclass, and the target instantiates its generic supertype with a type variable in scope
    // where the value has a wildcard. The subclass's own class signature gives that supertype
    // view; the wildcard is never literally the variable, so the instantiations are not in an
    // invariant assignment, and the source cast the value to the target. The cast's erasure is
    // the supertype the value already implements, so javac emits no checkcast for it.
    if (!doCastGenerics
      && contextIndependentValue(exprent)
      && wildcardSubtypeTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }

    // A target of array type whose element is a type variable of the enclosing source, against a
    // value whose array element is a different type: no implicit conversion exists (arrays are
    // covariant only over reifiable element types), so a source that compiled cast the value to
    // that same array type. The call's recorded signature proves the target; the cast erases to
    // the variable's erasure, so javac either elides the checkcast or the target already has it.
    if (!doCastGenerics
      && typeVariableArrayTarget(exprent.getNamedGenerics(), leftType, rightType)) {
      doCastGenerics = true;
    }

    // A cast whose type argument is a generic class written bare cannot come from a source that
    // compiled: every class file records generic types in full, so a bare argument here is the
    // printer's own inference losing arguments, and F<Bare> is not a conversion javac accepts from
    // the value's recorded F<?> or F<Concrete>. Dropping the cast lets javac infer the argument
    // again, which is what the original source did.
    if (doCastGenerics && hasRawTypeArgument(leftType)) {
      doCastGenerics = false;
    }

    // A static generic factory chain whose result the printer already types exactly as the
    // context target still prints a generic cast at every leaf argument the target's variable
    // substitution contradicts the argument's recorded type at. Those casts are not conversions
    // the class file records - their erasures already match - they are the printer showing the
    // target's substitution. The source wrote one cast around the whole call instead: under it
    // javac infers the chain from the arguments alone, every leaf takes its argument's recorded
    // type, and the unbounded-wildcard intermediate makes the conversion unchecked. Print that
    // cast and re-infer the chain standalone (the cast is not a poly context).
    boolean hoistedResultCast = false;
    if (!castAlways && !InvocationExprent.insideOwnArgumentList()
      && !doCast && !doCastNull && !doCastNarrowing && !doCastGenerics
      && exprent instanceof InvocationExprent resultCall
      && resultCall.isStatic() && resultCall.isPolyCall()
      && leftType instanceof GenericType resultTarget
      && resultTarget.getWildcard() == GenericType.WILDCARD_NO && resultTarget.arrayDim == 0
      && resultTarget.value != null
      && rightType != null && sameErasedType(rightType, leftType)
      && sameErasedType(resultCall.getDescriptor().ret, leftType)
      && unboundedClassParameters(resultTarget.value)
      && hoistCastInstantiationNameable(leftType, exprent.getNamedGenerics())
      && resultCall.conflictingArgumentCasts() >= 2) {
      hoistedResultCast = true;
    }

    // An instantiation of X cannot be cast to another instantiation of X whose arguments are
    // provably distinct: javac rejects the conversion outright. In an argument list the printer
    // seeded a type variable from the call's own context and javac infers it again from the
    // value, which is what the original relied on; elsewhere the source widened the value to a
    // wildcard instantiation first, and that intermediate cast is an unchecked one javac accepts.
    boolean castRaw = false;
    boolean doubleCast = hoistedResultCast;
    VarType doubleCastTarget = leftType;
    VarType doubleCastInner = null;
    VarType wildcardOnlyCast = null;
    VarType receiverCastTarget = null;
    if (doCastGenerics && !castAlways && !doCast && !doCastNull && !doCastNarrowing
      && provablyInconvertible(leftType, rightType)) {
      if (InvocationExprent.inArgument()) {
        doCastGenerics = false;
      } else {
        receiverCastTarget = doubleCastReceiverCast(exprent, leftType, rightType);
        if (receiverCastTarget == null) {
          doubleCastInner = uncheckedDoubleCastInner(leftType, rightType);
          if (doubleCastInner != null) {
            doubleCast = true;
            doubleCastTarget = leftType;
          } else {
            castRaw = true;
          }
        }
      }
    }

    // A functional argument whose inferred SAM return is a type variable neither side can name
    // produces a capture. When the target instantiates the same class with a type variable of
    // the caller, the call's own variable is constrained by the target to that named variable
    // and by the argument to the capture, so no instantiation satisfies both and javac rejects
    // the call; a source that compiled cast the result. The cast erases to the class the call
    // already returns, so it emits no checkcast. A target with a wildcard accepts the capture,
    // and a target with a concrete argument lets javac infer the variable from that target, so
    // neither needs a cast.
    if (!doCastGenerics
      && exprent instanceof InvocationExprent
      && leftType instanceof GenericType && leftType.type == CodeType.OBJECT && leftType.arrayDim == 0
      && !hasWildcard(leftType) && !hasRawTypeArgument(leftType)
      && rightType != null && rightType.isGeneric() && rightType.type == CodeType.OBJECT
      && rightType.value != null && rightType.value.equals(leftType.value)
      && hasInScopeTypeVariable(leftType, exprent.getNamedGenerics())
      && captureReturnedArgument(exprent)) {
      doCastGenerics = true;
    }

    // A target type that still names a type parameter of the callee which inference left unbound
    // has no nameable form at the call site, so a compiling source cannot have written a cast
    // built on it. Passing the expression on lets javac infer the callee's variable again. The
    // lattice conversion to a bare type variable is a cast like any other: the argument's own
    // recorded type is at or below the variable's erasure, and javac infers the callee's variable
    // from it.
    if ((doCastGenerics || doCast) && InvocationExprent.namesUnboundArgumentVariable(leftType)) {
      doCastGenerics = false;
      doCast = false;
      castRaw = false;
    }

    // A cast from an instantiation whose type argument is a wildcard capture to another
    // instantiation is illegal under JLS 5.5.1 unless the target's argument is the wildcard's
    // own bound (or below it): javac rejects the printed conversion outright. The source that
    // compiled widened to a wildcard instantiation first (an unchecked cast javac accepts), and
    // that two-step form falls back to the raw erasure when no intermediate exists. All steps
    // erase to the same class, so the class file is unchanged.
    if (doCastGenerics && !castRaw && !doubleCast && receiverCastTarget == null
      && parameterizedCastIllegal(leftType, rightType)) {
      doubleCastInner = uncheckedDoubleCastInner(leftType, rightType);
      if (doubleCastInner != null) {
        doubleCast = true;
        doubleCastTarget = leftType;
      } else {
        castRaw = true;
      }
    }

    // An argument whose parameter is the raw class G but whose value is a parameterized subtype
    // of G: our solution for the callee's G<A> is the subtype's own argument, a capture javac
    // cannot use. The subtype's recorded supertype view names the parameterization the source
    // cast to (TaggedChoiceType<?> as Type<Pair<?,?>>); that view's instantiation is provably
    // distinct from the subtype's, so the source widened to the erased G first. Both steps erase
    // to the parameter's own class, so no checkcast can appear.
    if (!doCastGenerics && !doCast && !castRaw && !doCastNull && !doCastNarrowing && !castAlways
      && leftType != null && leftType.type == CodeType.OBJECT && leftType.arrayDim == 0 && !leftType.isGeneric()
      && exprent instanceof InvocationExprent
      && rightType instanceof GenericType typedValue && typedValue.getWildcard() == GenericType.WILDCARD_NO
      && typedValue.type == CodeType.OBJECT && typedValue.value != null
      && !typedValue.value.equals(leftType.value)
      && DecompilerContext.getStructContext().instanceOf(typedValue.value, leftType.value)) {
      VarType view = GenericType.getGenericSuperType(typedValue, new VarType(CodeType.OBJECT, 0, leftType.value));
      boolean[] captured = new boolean[1];
      view = wildcardUnnameableInView(view, exprent.getNamedGenerics(), captured);
      // In an argument list whose parameter type variable nothing else constrains, javac infers
      // that variable from this argument's own recorded type: the value's supertype view already
      // is the target, and the source passed it bare.
      boolean argumentInferred = InvocationExprent.inArgument()
        && InvocationExprent.currentArgumentVariableUnconstrained();
      // Where the variable is constrained only in a functional interface's input positions, the
      // wildcard form's capture is accepted there and the invariant outer layer is the printer's.
      boolean wildcardAccepted = InvocationExprent.inArgument()
        && InvocationExprent.currentArgumentVariableWeakenable();
      if (captured[0] && view instanceof GenericType superView && leftType.value.equals(superView.value)
        && superView.getWildcard() == GenericType.WILDCARD_NO && !superView.equalsExact(typedValue)
        && !invalidGenericInstantiation(superView) && unboundedClassParameters(superView.value)
        && !argumentInferred) {
        VarType wildcardForm = wildcardAccepted ? strictDoubleCastInner(superView) : null;
        if (wildcardForm != null) {
          wildcardOnlyCast = wildcardForm;
        } else {
          doubleCastTarget = superView;
          doubleCast = true;
        }
      }
    }

    // A generic call whose type variables our inference could only leave at their erasure (the
    // value's type is the raw class) against a parameterized target: javac re-infers the call
    // from the target and cannot solve the callee's own variables. The call's recorded return
    // Signature names the instantiation once its unnameable variables are wildcarded, and when
    // that instantiation is exactly the target, the source cast to the erased form first and
    // then to the target. Both erase to the target's class, so no checkcast can appear.
    // In an argument list the parameter's instantiation is the printer's own inference from this
    // argument, so javac solves the same variables again from the bare value and the source wrote
    // none of it; only a target recorded independently of the value (a field, a return) needs the
    // cast.
    if (!doubleCast && !doCastGenerics && !doCast && !castRaw && !doCastNull && !doCastNarrowing && !castAlways
      && leftType instanceof GenericType erasureTarget && erasureTarget.getWildcard() == GenericType.WILDCARD_NO
      && erasureTarget.arrayDim == 0 && !erasureTarget.getArguments().isEmpty()
      && !invalidGenericInstantiation(leftType) && unboundedClassParameters(erasureTarget.value)
      && exprent instanceof InvocationExprent erasureCall
      && rightType != null && rightType.type == CodeType.OBJECT && !rightType.isGeneric()
      && erasureTarget.value.equals(rightType.value)) {
      boolean[] wildcarded = new boolean[1];
      VarType named = wildcardUnnameableInView(erasureCall.getDeclaredGenericReturnType(),
        exprent.getNamedGenerics(), wildcarded);
      if (wildcarded[0] && named instanceof GenericType namedType
        && namedType.getWildcard() == GenericType.WILDCARD_NO
        && namedType.equalsExact(erasureTarget)
        && !InvocationExprent.inArgument()) {
        doubleCastTarget = erasureTarget;
        doubleCast = true;
      }
    }

    // A field whose recorded type is a wildcard-ed generic (Codec<? extends Schema<?>>) passed
    // to a parameterized parameter: the value's argument is a capture, which the parameter's
    // variable cannot be inferred from, so the source cast the field to the wildcard's bound
    // instantiation (Codec<Schema<?>>). Both types are recorded - the field's Signature and the
    // parameter's - and the cast erases to the class the value already has.
    boolean fieldBoundCast = false;
    VarType fieldBoundTarget = null;
    if (!castAlways && !doCast && !doCastGenerics && !castRaw && !doCastNull && !doCastNarrowing && !doubleCast
      && exprent instanceof FieldExprent
      // A target that is not itself generic accepts the field as it is; casting to a bound
      // instantiation there converts nothing. A wildcard target (`? extends MapCodec<? extends
      // T>`, a lambda's SAM return) is not a parameterized type either: the wildcard accepts the
      // field's own instantiation, so there is no conversion to print.
      && leftType instanceof GenericType targetGeneric && targetGeneric.getWildcard() == GenericType.WILDCARD_NO
      // An argument whose declared parameter already takes the field's recorded type under this
      // argument's own instantiation needs no conversion.
      && !(InvocationExprent.inArgument() && InvocationExprent.currentArgumentAcceptsDeclared(rightType, exprent.getNamedGenerics()))
      // A target that already accepts the field's recorded type needs no conversion either: the
      // value assigns through its supertype view (`ImmutableList<? extends X>` to
      // `Collection<? extends X>`) or its wildcard lies inside the target's
      // (`ResourceKey<? extends Registry<T>>` to `ResourceKey<? extends Registry<? extends T>>`).
      // The bound cast is the printer's showing; the source assigned the field bare. A target
      // that is exactly the field's own recorded type proves nothing: the parameter's variable
      // was substituted from this value itself, and the bound cast is what guides the call's
      // inference there.
      && !(rightType instanceof GenericType recordedFieldType && !recordedFieldType.equalsExact(leftType)
        && GenericType.isAssignable(rightType, leftType, exprent.getNamedGenerics()))
      && rightType instanceof GenericType fieldType && fieldType.getWildcard() == GenericType.WILDCARD_NO
      && fieldType.type == CodeType.OBJECT && fieldType.arrayDim == 0 && fieldType.getArguments().size() == 1
      && fieldType.getArguments().get(0) instanceof GenericType boundWildcard
      && boundWildcard.getWildcard() == GenericType.WILDCARD_EXTENDS && boundWildcard.value != null
      && unboundedClassParameters(fieldType.value)) {
      VarType bound = GenericType.withWildcard(boundWildcard, GenericType.WILDCARD_NO);
      VarType target = new GenericType(CodeType.OBJECT, 0, fieldType.value, null,
        Collections.singletonList(bound), GenericType.WILDCARD_NO);
      if (!invalidGenericInstantiation(target)) {
        fieldBoundTarget = target;
        fieldBoundCast = true;
      }
    }

    // A ternary of in-range int constants narrowed to a byte, short or char target: the source's
    // arms were constants of the target type (a constant cast folds to the same immediate), and
    // the class file holds no i2b/i2c for the assignment. Printing the outer cast would add one.
    boolean narrowTernaryCast = false;
    if (doCast && exprent instanceof FunctionExprent narrowTernary
      && narrowTernary.narrowConstantArms(leftType)) {
      doCast = false;
      narrowTernaryCast = true;
    }

    // An argument that is an untyped lambda parameter of the lambda being printed: its tracked
    // type is the synthetic body method's erased slot (Object), not a type the source wrote.
    // When the declared parameter is a bare type variable that the printer substituted by exactly
    // this cast target, and the parameter erases to Object, the cast converts nothing: javac
    // infers the variable and the untyped parameter from this same call context, and the cast is
    // the printer's own substitution showing. The called method's own variables are re-inferred
    // from the arguments; a class variable counts only when the receiver's recorded instantiation
    // genuinely substitutes it (see currentParameterIsSubstitutedVariable). An overload-choice
    // cast selects the overload, and the parameter's own erasure is what it works around; both are
    // excluded.
    if (!castAlways && InvocationExprent.inArgument()
      && exprent instanceof VarExprent lambdaParameter
      && lambdaParameter.hasLambdaParameterType()
      && sameType(lambdaParameter.getLambdaParameterType(), VarType.VARTYPE_OBJECT)
      && leftType != null && leftType.type == CodeType.GENVAR && leftType.arrayDim == 0
      && InvocationExprent.currentParameterIsSubstitutedVariable(leftType)) {
      doCast = false;
      doCastGenerics = false;
      doubleCast = false;
      wildcardOnlyCast = null;
      castRaw = false;
      fieldBoundCast = false;
    }

    // In an argument list the parameter type is not fixed by the source: javac instantiates the
    // called method's own variables from the arguments and the context. When the value's recorded
    // type already fits the declared parameter under such an instantiation, every generic-cast
    // reason above is the printer's own substitution showing, and the source passed the value
    // bare. The same holds for a cast to a bare type variable of the called method, which javac
    // re-infers from the argument list. An overload-choice cast is excluded: it selects the
    // overload, not the variable.
    boolean inferenceTarget = doCast && InvocationExprent.inArgument()
      && InvocationExprent.currentParameterTargetIsInferenceOnly(leftType);
    if (!castAlways && InvocationExprent.inArgument()
      && (doCastGenerics || doubleCast || wildcardOnlyCast != null || castRaw || fieldBoundCast
          || inferenceTarget)
      && InvocationExprent.currentArgumentAcceptsDeclared(rightType, exprent.getNamedGenerics())) {
      doCastGenerics = false;
      doubleCast = false;
      wildcardOnlyCast = null;
      castRaw = false;
      fieldBoundCast = false;
      if (inferenceTarget) {
        doCast = false;
      }
    }

    // An overload-choice cast on a variable the table records at the parameter's own primitive
    // type selects nothing: no reference overload is a candidate, and no numeric conversion is
    // performed. The printer's inference alone is not enough — it may have widened away the
    // recorded type that the cast was re-narrowing.
    boolean samePrimitive = castAlways && leftType.equals(rightType) && isPrimitive(leftType)
      && recordedPrimitiveMatches(exprent, leftType);
    boolean cast = ((castAlways && !narrowTernaryCast && !samePrimitive) || doCast || doCastNull
      || doCastNarrowing || doCastGenerics || doubleCast || wildcardOnlyCast != null
      || fieldBoundCast) && !exactRecordedType;

    // A switch expression is poly: javac types every arm from the context target and emits no
    // cast after the merge, so an outer cast is the printer's. A `case null` does not on its own
    // decide the merge's type, but the target still types every arm: when each simple arm
    // provably fits it, the merge is the target and the source needed no cast. When an arm's
    // recorded arguments pin its variable to a class the target rejects, no poly switch can
    // typecheck; the source cast the switch's result instead, so that cast is the source's and
    // the arms print standalone.
    if (exprent instanceof SwitchExprent switchCast) {
      if (switchCast.simpleArmsFitTarget(leftType)) {
        cast = false;
      } else if (leftType != null && switchCast.armsNeedTargetCast(leftType)) {
        cast = true;
      }
    }

    // A call chain whose receiver records an unbounded wildcard and whose functional argument
    // types the call's variable from its own body: the target never pinned that variable, and
    // javac (in the source's cast context) infers the chain standalone. When the call prints no
    // witness (or only the callee's own unresolved name, the printer's projection of the target
    // onto it), the source could not have typed it here and cast the result instead; print that
    // one cast outside the chain.
    if (!cast && leftType != null && functionalBodyTargetDropped
      && exprent instanceof InvocationExprent openCall
      && (!openCall.printsWitness() || openCall.witnessRepeatsDroppedVariable())) {
      cast = true;
    }

    // A raw generic argument passed to a parameterized parameter whose variables the call's
    // other arguments fix: the source's implicit unchecked conversion can be written explicitly
    // as a cast to the complete instantiation, which turns the call's own unchecked conversion
    // into one checked argument. Only a complete, nameable instantiation is printed; an erased,
    // wildcard or unresolved argument disqualifies the site.
    if (!cast && !castAlways && InvocationExprent.inArgument()
      && (exprent instanceof VarExprent || exprent instanceof FieldExprent)
      && rightType != null && rightType.type == CodeType.OBJECT && rightType.arrayDim == 0
      && !rightType.isGeneric() && rightType.value != null
      && leftType instanceof GenericType argumentTarget && argumentTarget.type == CodeType.OBJECT
      && argumentTarget.arrayDim == 0 && argumentTarget.getWildcard() == GenericType.WILDCARD_NO
      && !argumentTarget.getArguments().isEmpty()
      && rightType.value.equals(argumentTarget.value)
      && !hasWildcard(leftType) && !hasRawTypeArgument(leftType)
      && isNameableCastInstantiation(leftType, exprent.getNamedGenerics())
      && InvocationExprent.currentArgumentParameterFixedByCall()) {
      cast = true;
    }

    // A raw generic argument whose parameter's variable no sibling mentions: javac can only
    // infer that variable from this value, so the implicit unchecked conversion is the sole
    // instantiation and no complete one can be named. The source's conversion is writable as a
    // cast to the all-wildcard instantiation (`(G<?>) raw`), one checked conversion in place of
    // the call's implicit one. The wildcard form must be nameable; the value's class must be
    // the parameter's own class.
    if (!cast && !castAlways && InvocationExprent.inArgument()
      && InvocationExprent.isDirectArgument(exprent)
      && (exprent instanceof VarExprent || exprent instanceof FieldExprent)
      && rightType != null && rightType.type == CodeType.OBJECT && rightType.arrayDim == 0
      && !rightType.isGeneric() && rightType.value != null
      && (leftType == null || leftType.value == null || rightType.value.equals(leftType.value))
      && InvocationExprent.currentArgumentVariableInferredFromValue()) {
      VarType wildcard = wildcardArgumentInstantiation(rightType.value);
      if (wildcard != null && isNameableCastInstantiation(wildcard, exprent.getNamedGenerics())) {
        wildcardOnlyCast = wildcard;
        cast = true;
      }
    }

    // A raw generic argument of a subclass passed to a parameterized supertype the signature
    // fixes without any of the called method's own variables: javac converts the value
    // implicitly and infers nothing from it, so the source's unchecked conversion is writable as
    // a cast to the complete instantiation, one checked argument in place of the call's implicit
    // one. The cast is a widening reference conversion to the parameter's erasure, so javac emits
    // no checkcast for it. A same-class raw value is covered by the sites above; only a complete,
    // nameable instantiation is printed, and a parameter still naming a callee variable is
    // excluded because a cast there would pin an inference javac had left open.
    if (!cast && !castAlways && InvocationExprent.inArgument()
      && InvocationExprent.isDirectArgument(exprent)
      && (exprent instanceof VarExprent || exprent instanceof FieldExprent)
      && rightType != null && rightType.type == CodeType.OBJECT && rightType.arrayDim == 0
      && !rightType.isGeneric() && rightType.value != null
      && isGenericClass(rightType.value)
      && leftType instanceof GenericType argumentTarget && argumentTarget.type == CodeType.OBJECT
      && argumentTarget.arrayDim == 0 && argumentTarget.getWildcard() == GenericType.WILDCARD_NO
      && !argumentTarget.getArguments().isEmpty() && !rightType.value.equals(argumentTarget.value)
      && DecompilerContext.getStructContext().instanceOf(rightType.value, argumentTarget.value)
      && !hasWildcard(leftType) && !hasRawTypeArgument(leftType)
      && !hasInScopeTypeVariable(leftType, exprent.getNamedGenerics())
      && isNameableCastInstantiation(leftType, exprent.getNamedGenerics())
      && InvocationExprent.currentArgumentParameterFixedBySignature()) {
      cast = true;
    }

    if (castNull == NullCastType.DONT_CAST_AT_ALL && rightType.type == CodeType.NULL) {
      cast = castAlways;
    }

    // A class type variable cannot be named from a static method, so the original source cannot
    // have had this cast; drop it and let the expression's own type stand.
    boolean castLambda = !cast && exprent instanceof NewExprent && !leftType.equals(rightType) &&
                          lambdaNeedsCast(leftType, (NewExprent)exprent);

    boolean quote = cast && exprent.getPrecedence() >= FunctionType.CAST.precedence;

    // cast instead to 'byte' / 'short' when int constant is used as a value for 'Byte' / 'Short'
    if (castNarrowing && exprent instanceof ConstExprent && !((ConstExprent) exprent).isNull()) {
      if (leftType.equals(VarType.VARTYPE_BYTE_OBJ)) {
        leftType = VarType.VARTYPE_BYTE;
      }
      else if (leftType.equals(VarType.VARTYPE_SHORT_OBJ)) {
        leftType = VarType.VARTYPE_SHORT;
      }
    }

    if (cast) {
      VarType castType = wildcardOnlyCast != null ? wildcardOnlyCast
        : fieldBoundCast ? fieldBoundTarget
        : doubleCast ? doubleCastTarget
        : castRaw ? new VarType(leftType.type, leftType.arrayDim, leftType.value) : leftType;
      List<org.jetbrains.java.decompiler.util.Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> castAnnotations =
        castAnnotations(exprent);
      if (castAnnotations.isEmpty()) {
        buffer.append('(').appendCastTypeName(castType).append(')');
      }
      else {
        // The target records a cast expression whose operand ends at this expression: the source
        // wrote the annotation on the cast's own type, `(@Nullable T) value`.
        buffer.append('(').appendCastTypeName(castType, castAnnotations, Collections.emptySet()).append(')');
      }
      if (doubleCast) {
        // The first step widens the value to the strictest type the second cast accepts: the
        // target class with its one argument as an upper bound (`Type<? extends Pair<?, ?>>`).
        // When the target itself is the wildcarded erasure (`Dynamic<?>`), no first step exists
        // and printing it again would only repeat the same cast.
        VarType inner = doubleCastInner != null ? doubleCastInner : strictDoubleCastInner(doubleCastTarget);
        if (inner == null) {
          inner = erasedWildcardForm(doubleCastTarget);
        }
        if (!getCastTypeName(inner).equals(getCastTypeName(castType))) {
          buffer.append('(').appendCastTypeName(inner).append(')');
        }
      }
    }

    if (castLambda) {
      // The lambda's own type is the functional interface the target names; when the target is a
      // supertype of it, the interface's recorded declaration supplies the type arguments the
      // source wrote on the cast.
      VarType lambdaCast = castInstantiationFromUpperBound(rightType, leftType, exprent.getNamedGenerics());
      buffer.append('(').appendCastTypeName(lambdaCast != null ? lambdaCast : rightType).append(')');
    }

    if (quote) {
      buffer.append('(');
    }

    if (exprent instanceof ConstExprent) {
      ((ConstExprent) exprent).adjustConstType(leftType);
    }

    if (cast) {
      // Don't cast vararg array creation! Force regular array creation instead
      if (exprent instanceof NewExprent && ((NewExprent)exprent).isVarArgParam()) {
        ((NewExprent) exprent).setVarArgParam(false);
      }
    }

    // A printed cast is not a poly context: the call inside it is inferred from its arguments
    // alone, so the target recorded during this pass does not pin its type variables.
    if (cast && exprent instanceof InvocationExprent castCall) {
      castCall.setPrintedUnderCast(true);
      if (functionalBodyTargetDropped || hoistedResultCast) {
        // The witness the target-derived pass proved is the callee's own unresolved variable,
        // not a type the source named: infer the call standalone, as the cast context does.
        castCall.reinferUnderCast();
      }
    }
    // A switch is handed the target only when it prints bare and poly; inside a printed cast
    // javac types it standalone, and the cast converts the merged result.
    if (exprent instanceof SwitchExprent switchTarget) {
      switchTarget.setPrintTarget(cast ? null : leftType);
    }
    try {
      if (cast && receiverCastTarget != null && exprent instanceof InvocationExprent receiverCall) {
        // The two-step conversion is carried by the receiver instead of the result: the value the
        // call sees is the same erased receiver, so this prints byte-identical code.
        receiverCall.setReceiverCastTarget(receiverCastTarget);
        try {
          buffer.append(exprent.toJava(indent));
        } finally {
          receiverCall.clearReceiverCastTarget();
        }
      } else {
        buffer.append(exprent.toJava(indent));
      }
    } finally {
      if (cast && exprent instanceof InvocationExprent castCall) {
        castCall.setPrintedUnderCast(false);
      }
    }

    if (quote) {
      buffer.append(')');
    }

    return cast;
  }

  public enum NullCastType {
    CAST(true), // old boolean true
    DONT_CAST(false), // old boolean false
    DONT_CAST_AT_ALL(false); // old boolean false and don't cast

    private final boolean cast;

    NullCastType(boolean cast) {
      this.cast = cast;
    }
  }

  /**
   * Whether a cast from {@code right} to {@code left} is one javac rejects: both are the same
   * generic class and some pair of arguments is provably distinct, so neither instantiation is a
   * subtype of the other and the conversion is not an unchecked one either. Only the invariant
   * case is judged; wildcard targets, raw values and type variables keep the existing rules.
   */
  private static boolean provablyInconvertible(VarType left, VarType right) {
    if (!(left instanceof GenericType target) || !(right instanceof GenericType value)) {
      return false;
    }
    if (target.getWildcard() != GenericType.WILDCARD_NO || value.getWildcard() != GenericType.WILDCARD_NO
      || target.arrayDim != 0 || value.arrayDim != 0 || !target.value.equals(value.value)) {
      return false;
    }
    List<VarType> targetArgs = target.getArguments();
    List<VarType> valueArgs = value.getArguments();
    if (targetArgs.size() != valueArgs.size() || target.equalsExact(value)) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      if (argumentProvablyDistinct(targetArgs.get(i), valueArgs.get(i))) {
        return true;
      }
    }
    return false;
  }

  /**
   * The intermediate a two-step conversion to a provably distinct instantiation widens to: the
   * cast class with the value's own argument as an upper bound, its type variables wildcarded.
   * The first cast is an unchecked conversion javac accepts from the value, and the second from
   * that wildcard instantiation to the target.
   */
  private static @Nullable VarType uncheckedDoubleCastInner(VarType target, VarType value) {
    if (!(target instanceof GenericType targetType) || !(value instanceof GenericType valueType)
      || targetType.getWildcard() != GenericType.WILDCARD_NO || valueType.getWildcard() != GenericType.WILDCARD_NO
      || target.value == null || !target.value.equals(value.value)
      || targetType.getArguments().size() != 1 || valueType.getArguments().size() != 1) {
      return null;
    }
    VarType valueArgument = valueType.getArguments().get(0);
    if (valueArgument == null) {
      return null;
    }
    VarType bound = valueArgument instanceof GenericType generic
      && generic.getWildcard() == GenericType.WILDCARD_EXTENDS
      ? GenericType.withWildcard(generic, GenericType.WILDCARD_NO) : valueArgument;
    bound = wildcardUnnameableInView(bound, Collections.emptyMap(), new boolean[1]);
    if (bound == null) {
      return null;
    }
    VarType wildcard = GenericType.withWildcard(bound, GenericType.WILDCARD_EXTENDS);
    return new GenericType(CodeType.OBJECT, 0, target.value, null,
      Collections.singletonList(wildcard), GenericType.WILDCARD_NO);
  }

  /**
   * The receiver instantiation that lets a call's result reach the context target through a single
   * cast, or null when the receiver is not the value the second step would have to widen.
   *
   * <p>A class variable the method returns in a result position, mentioned by no parameter, ties
   * the result's instantiation to the receiver's: the recorded receiver type fixes the variable,
   * and the call's recorded return is exactly that substitution. The double cast would widen the
   * result's argument to its upper bound and cast that to the target; instantiating the receiver's
   * variable with the same wildcard makes the call itself return the widened type, so the source's
   * second conversion disappears. Both casts erase to the receiver's own class, so the class file
   * is unchanged.
   */
  private static @Nullable VarType doubleCastReceiverCast(Exprent exprent, VarType leftType, VarType rightType) {
    if (leftType == null || rightType == null
      || !(exprent instanceof InvocationExprent call) || call.isStatic() || call.getInstance() == null
      || !(call.getInstance() instanceof FieldExprent || call.getInstance() instanceof VarExprent)) {
      return null;
    }
    StructClass receiverClass = DecompilerContext.getStructContext().getClass(call.getClassname());
    if (receiverClass == null || receiverClass.getSignature() == null
      || receiverClass.getSignature().fparameters.isEmpty()) {
      return null;
    }
    StructMethod method = call.getDesc();
    if (method == null || method.getSignature() == null) {
      return null;
    }
    GenericMethodDescriptor signature = method.getSignature();
    VarType declaredReturn = signature.returnType;
    if (!(declaredReturn instanceof GenericType returned) || declaredReturn.type != CodeType.OBJECT
      || declaredReturn.arrayDim != 0 || returned.getWildcard() != GenericType.WILDCARD_NO
      || declaredReturn.value == null || leftType.value == null
      || !declaredReturn.value.equals(leftType.value)) {
      return null;
    }
    // The variable must link the receiver to the result directly: exactly one result argument is
    // a type variable of the receiver's class.
    int index = -1;
    for (int i = 0; i < returned.getArguments().size(); i++) {
      VarType argument = returned.getArguments().get(i);
      if (plainTypeVariable(argument) && receiverClass.getSignature().fparameters.contains(argument.value)) {
        if (index >= 0) {
          return null;
        }
        index = i;
      }
    }
    if (index < 0) {
      return null;
    }
    String variable = returned.getArguments().get(index).value;
    int classIndex = receiverClass.getSignature().fparameters.indexOf(variable);
    if (classIndex < 0) {
      return null;
    }
    // A parameter that mentions the variable constrains it from the call's argument list; the
    // receiver would then not be the only source of its instantiation.
    for (VarType parameter : signature.parameterTypes) {
      if (mentionsVariable(parameter, variable)) {
        return null;
      }
    }
    VarType receiverType = call.getInstance().getInferredExprType(null);
    if (!(receiverType instanceof GenericType receiver) || receiverType.type != CodeType.OBJECT
      || receiverType.arrayDim != 0 || !call.getClassname().equals(receiverType.value)
      || receiver.getArguments().size() != receiverClass.getSignature().fparameters.size()) {
      return null;
    }
    VarType receiverArgument = receiver.getArguments().get(classIndex);
    if (receiverArgument == null) {
      return null; // an unbounded wildcard leaves nothing to widen
    }
    Map<VarType, VarType> toReceiver = new HashMap<>();
    toReceiver.put(GenericType.parse("T" + variable + ";"), receiverArgument);
    if (!sameType(declaredReturn.remap(toReceiver), rightType)) {
      return null;
    }
    // The double cast's intermediate is the result widened by one wildcard; the same wildcard on
    // the receiver's variable is the widening the source actually wrote.
    VarType intermediate = uncheckedDoubleCastInner(leftType, rightType);
    if (!(intermediate instanceof GenericType intermediateType)
      || intermediateType.getArguments().size() != 1) {
      return null;
    }
    VarType wildcard = intermediateType.getArguments().get(0);
    List<VarType> castArguments = new ArrayList<>(receiver.getArguments());
    castArguments.set(classIndex, wildcard);
    VarType cast = new GenericType(CodeType.OBJECT, 0, receiverType.value, receiver.getParent(),
      castArguments, receiver.getWildcard());
    if (!isNameableCastInstantiation(cast, exprent.getNamedGenerics())
      || !(cast instanceof GenericType castType)) {
      return null;
    }
    // The source cast must be a widening, never a narrowing: every argument either keeps its
    // instantiation or is a wildcard that contains it.
    return instantiationContains(castType, receiver) ? cast : null;
  }

  /** Whether every type argument of {@code outer} contains the same position of {@code inner}. */
  private static boolean instantiationContains(GenericType outer, GenericType inner) {
    if (outer.value == null || !outer.value.equals(inner.value)
      || outer.getWildcard() != GenericType.WILDCARD_NO || inner.getWildcard() != GenericType.WILDCARD_NO
      || outer.getArguments().size() != inner.getArguments().size()) {
      return false;
    }
    for (int i = 0; i < outer.getArguments().size(); i++) {
      VarType outerArgument = outer.getArguments().get(i);
      VarType innerArgument = inner.getArguments().get(i);
      if (outerArgument == null) {
        continue; // an unbounded wildcard contains every instantiation
      }
      if (outerArgument instanceof GenericType wildcard
        && wildcard.getWildcard() == GenericType.WILDCARD_EXTENDS) {
        if (!boundContainsTarget(GenericType.withWildcard(wildcard, GenericType.WILDCARD_NO), innerArgument)) {
          return false;
        }
        continue;
      }
      if (!sameType(outerArgument, innerArgument)) {
        return false;
      }
    }
    return true;
  }

  /** Whether the type mentions the named type variable at or below this position. */
  private static boolean mentionsVariable(VarType type, String variable) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR && variable.equals(type.value)) {
      return true;
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (mentionsVariable(argument, variable)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * The strictest type a double cast's first step can widen to, or null when the target names no
   * argument. A single upper-bounded argument is the form that still accepts the target cast: the
   * value is castable to the target class with its argument as an upper bound, and that in turn to
   * the target itself.
   */
  private static VarType strictDoubleCastInner(VarType target) {
    if (!(target instanceof GenericType generic) || generic.getArguments().size() != 1
        || generic.getArguments().get(0) == null) {
      return null;
    }
    VarType bound = GenericType.withWildcard(generic.getArguments().get(0), GenericType.WILDCARD_EXTENDS);
    return new GenericType(CodeType.OBJECT, 0, target.value, null,
      java.util.Collections.singletonList(bound), GenericType.WILDCARD_NO);
  }

  /**
   * A declared type with every type variable wildcarded, or null when the type itself is one.
   *
   * <p>A method reference records its instantiated type erased, so a type variable the source
   * pinned is only recoverable from the referenced method's declaration. The wildcard is the one
   * nameable form of an argument no source spelled, and writing it back is byte-neutral.
   */
  public static VarType wildcardUnnameableType(VarType type) {
    boolean[] captured = new boolean[1];
    VarType value = wildcardUnnameableInView(type, java.util.Collections.emptyMap(), captured);
    return captured[0] ? value : null;
  }

  /**
   * Replaces every type variable not recorded at the call site with the unbounded wildcard,
   * reporting whether any was replaced: such a position is a capture, the value our inference
   * could not name.
   */
  private static VarType wildcardUnnameableInView(VarType type, Map<VarType, List<VarType>> named,
                                                  boolean[] captured) {
    if (type == null) {
      return null;
    }
    if (type.type == CodeType.GENVAR) {
      if (Exprent.isTypeVariableNameable(type.resizeArrayDim(0), named)) {
        return type;
      }
      captured[0] = true;
      return null;
    }
    if (!(type instanceof GenericType generic) || generic.getArguments().isEmpty()) {
      return type;
    }
    List<VarType> arguments = new ArrayList<>(generic.getArguments().size());
    boolean changed = false;
    for (VarType argument : generic.getArguments()) {
      if (argument == null) {
        arguments.add(null);
        continue;
      }
      VarType value = wildcardUnnameableInView(argument, named, captured);
      if (value != argument) {
        changed = true;
      }
      arguments.add(value);
    }
    if (!changed) {
      return type;
    }
    return new GenericType(type.type, type.arrayDim, type.value, generic.getParent(),
      Collections.unmodifiableList(arguments), generic.getWildcard());
  }

  /**
   * Whether a class's type parameters are all unbounded: a wildcard argument is a legal cast
   * argument there. A self-referential bound (Builder&lt;T extends Builder&lt;T&gt;&gt;) rejects
   * the wildcard, so its subtypes' casts must not be invented.
   */
  private static boolean unboundedClassParameters(String internalName) {
    StructClass cls = DecompilerContext.getStructContext().getClass(internalName);
    if (cls == null || cls.getSignature() == null) {
      return true;
    }
    for (List<VarType> bounds : cls.getSignature().fbounds) {
      if (bounds != null && !bounds.isEmpty() && !VarType.VARTYPE_OBJECT.equals(bounds.get(0))) {
        return false;
      }
    }
    return true;
  }

  /** The erased form of a parameterized instantiation: its class with unbounded wildcards. */
  private static VarType erasedWildcardForm(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return new VarType(type.type, type.arrayDim, type.value);
    }
    List<VarType> arguments = new ArrayList<>(generic.getArguments().size());
    for (int i = 0; i < generic.getArguments().size(); i++) {
      arguments.add(null);
    }
    return new GenericType(CodeType.OBJECT, type.arrayDim, type.value, null,
      Collections.unmodifiableList(arguments), GenericType.WILDCARD_NO);
  }

  /**
   * The all-wildcard instantiation of a generic class: the one checked form of a raw argument's
   * conversion. Null when the class records no type parameters.
   */
  private static VarType wildcardArgumentInstantiation(String className) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null || cls.getSignature() == null || cls.getSignature().fparameters.isEmpty()) {
      return null;
    }
    List<VarType> arguments = new ArrayList<>(cls.getSignature().fparameters.size());
    for (int i = 0; i < cls.getSignature().fparameters.size(); i++) {
      arguments.add(null);
    }
    return new GenericType(CodeType.OBJECT, 0, className, null, arguments, GenericType.WILDCARD_NO);
  }

  /**
   * JLS 5.5.1 for the wildcard-capture shape: a cast to {@code X<Z>} from {@code X<? extends B<..>>}
   * is legal only when Z is contained by the wildcard's bound, i.e. Z is a subtype of B. A target
   * position that is itself a wildcard, or a type variable, is never provably distinct from the
   * value's wildcard and javac accepts the unchecked cast. Anything else is provably distinct and
   * javac rejects the cast; only the raw erasure compiles.
   */
  private static boolean parameterizedCastIllegal(VarType left, VarType right) {
    if (!(left instanceof GenericType target) || !(right instanceof GenericType value)
      || target.getWildcard() != GenericType.WILDCARD_NO || value.getWildcard() != GenericType.WILDCARD_NO
      || target.arrayDim != 0 || value.arrayDim != 0 || target.value == null || value.value == null
      || !target.value.equals(value.value)) {
      return false;
    }
    List<VarType> targetArgs = target.getArguments();
    List<VarType> valueArgs = value.getArguments();
    if (targetArgs.size() != valueArgs.size()) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      VarType targetArg = targetArgs.get(i);
      VarType valueArg = valueArgs.get(i);
      if (!(valueArg instanceof GenericType wildcard) || wildcard.getWildcard() != GenericType.WILDCARD_EXTENDS
        || !wildcard.isGeneric() || wildcard.getArguments().isEmpty() || wildcard.value == null) {
        continue;
      }
      // An unbounded `?` parses as null; like every wildcard target it is never provably distinct.
      if (targetArg == null || targetArg instanceof GenericType targetWildcard
        && targetWildcard.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      // A type variable is not provably distinct from a wildcard either.
      if (targetArg.type == CodeType.GENVAR) {
        continue;
      }
      // A wildcard bound that mentions a type variable fixes the cast's argument: the target must
      // be contained by that bound with the same variables. A target that drops or replaces one
      // is provably distinct (the capture could be a sibling subtype), and the source widened to
      // the bound with the variable wildcarded first.
      if (mentionsGenericVariable(wildcard)
        && !boundContainsTarget(GenericType.withWildcard(wildcard, GenericType.WILDCARD_NO), targetArg)) {
        return true;
      }
      // A concrete argument is contained by `? extends B` when it is a subtype of B: Integer is
      // legal under `? extends Number`, Object is not. The same erasure rule governs a
      // parameterized argument (WritableRegistry<?> under `? extends Registry<?>`), so only an
      // argument whose erasure is not below the bound forces the raw form.
      if (targetArg.type != CodeType.OBJECT || targetArg.arrayDim != 0 || targetArg.value == null
        || !DecompilerContext.getStructContext().instanceOf(targetArg.value, wildcard.value)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The instantiation of a recorded checkcast's target class that the context target names, or
   * null when the context does not fix one. The class file's checkcast names only the erasure;
   * a source cast must name an instantiation the context accepts, and when the value is not
   * assignable to the context the source's cast is what makes it so.
   */
  public static @Nullable VarType castInstantiationFromUpperBound(VarType erasedTarget, VarType upperBound,
                                                                  Map<VarType, List<VarType>> named) {
    if (erasedTarget == null || erasedTarget.type != CodeType.OBJECT || erasedTarget.value == null
      || upperBound == null || upperBound.type != CodeType.OBJECT || upperBound.value == null
      || upperBound.arrayDim != 0) {
      return null;
    }
    StructClass targetClass = DecompilerContext.getStructContext().getClass(erasedTarget.value);
    if (targetClass == null || targetClass.getSignature() == null
      || targetClass.getSignature().fparameters.isEmpty()) {
      return null;
    }

    VarType view = null;
    if (upperBound.value.equals(erasedTarget.value)) {
      view = upperBound;
    } else if (DecompilerContext.getStructContext().instanceOf(upperBound.value, erasedTarget.value)) {
      // The context target is a subtype of the cast class: its recorded supertype view names the
      // instantiation the cast expressed.
      view = GenericType.getGenericSuperType(upperBound, new VarType(CodeType.OBJECT, 0, erasedTarget.value));
    } else if (DecompilerContext.getStructContext().instanceOf(erasedTarget.value, upperBound.value)) {
      // The context target is a supertype of the cast class: instantiate the cast class's own
      // declaration through its recorded view of that supertype.
      VarType superView = GenericType.getGenericSuperType(targetClass.getSignature().genericType,
        new VarType(CodeType.OBJECT, 0, upperBound.value));
      if (superView != null && upperBound.value.equals(superView.value)) {
        Map<VarType, VarType> mapping = new HashMap<>();
        if (upperBound instanceof GenericType && superView instanceof GenericType
          && ((GenericType) upperBound).getArguments().size() == ((GenericType) superView).getArguments().size()) {
          ((GenericType) superView).mapGenVarsTo((GenericType) upperBound, mapping);
        }
        view = targetClass.getSignature().genericType.remap(mapping);
      }
    }

    if (!(view instanceof GenericType) || view.value == null || !view.value.equals(erasedTarget.value)) {
      return null;
    }
    return isNameableCastInstantiation(view, named) ? view : null;
  }

  /**
   * The instantiation of a recorded checkcast's target class that the operand itself records, or
   * null when the operand's type does not fix one. Only a local or field is read: its type is
   * written by the class file and needs no inference context.
   */
  public static @Nullable VarType castInstantiationFromOperand(VarType erasedTarget, Exprent operand,
                                                               Map<VarType, List<VarType>> named) {
    if (erasedTarget == null || erasedTarget.type != CodeType.OBJECT || erasedTarget.value == null || operand == null) {
      return null;
    }
    VarType value;
    if (operand instanceof VarExprent var) {
      value = var.getInferredExprType(null);
    } else if (operand instanceof FieldExprent field) {
      value = field.getInferredExprType(null);
    } else {
      return null;
    }

    VarType view = castOperandView(erasedTarget, value);
    if (view == null) {
      return null;
    }
    return isNameableCastInstantiation(view, named) ? view : null;
  }

  /** The target class's instantiation seen from the operand's recorded type, if any. */
  private static @Nullable VarType castOperandView(VarType erasedTarget, VarType value) {
    if (value == null || value.type != CodeType.OBJECT || value.value == null || value.arrayDim != 0) {
      return null;
    }
    StructClass targetClass = DecompilerContext.getStructContext().getClass(erasedTarget.value);
    if (targetClass == null || targetClass.getSignature() == null
      || targetClass.getSignature().fparameters.isEmpty()) {
      return null;
    }

    if (value.value.equals(erasedTarget.value) && value instanceof GenericType valueType) {
      // The same class: its recorded arguments are the source's instantiation. An upper-bounded
      // wildcard is the strongest nameable form of the argument and is what the source wrote
      // where the capture itself cannot be named.
      List<VarType> arguments = new ArrayList<>(valueType.getArguments().size());
      for (VarType argument : valueType.getArguments()) {
        if (argument instanceof GenericType generic
          && generic.getWildcard() == GenericType.WILDCARD_EXTENDS) {
          arguments.add(GenericType.withWildcard(generic, GenericType.WILDCARD_NO));
        } else {
          arguments.add(argument);
        }
      }
      return new GenericType(CodeType.OBJECT, 0, erasedTarget.value, null, arguments, GenericType.WILDCARD_NO);
    }
    if (DecompilerContext.getStructContext().instanceOf(value.value, erasedTarget.value)) {
      // The operand is a subclass of the cast class: its recorded supertype view is the answer.
      VarType view = GenericType.getGenericSuperType(value, new VarType(CodeType.OBJECT, 0, erasedTarget.value));
      return view != null && erasedTarget.value.equals(view.value) ? view : null;
    }
    if (DecompilerContext.getStructContext().instanceOf(erasedTarget.value, value.value)) {
      // The operand is a supertype of the cast class: solve the cast class's parameters from the
      // recorded instantiation through the hierarchy's own generic map.
      return solveCastInstantiation(targetClass, value);
    }
    return null;
  }

  private static @Nullable VarType solveCastInstantiation(StructClass targetClass, VarType value) {
    StructClass valueClass = DecompilerContext.getStructContext().getClass(value.value);
    if (valueClass == null || valueClass.getSignature() == null || !(value instanceof GenericType valueType)) {
      return null;
    }
    Map<VarType, VarType> hierarchy = targetClass.getAllGenerics().get(valueClass.qualifiedName);
    if (hierarchy == null || hierarchy.isEmpty()) {
      return null;
    }
    Map<VarType, VarType> actual = new HashMap<>();
    valueClass.getSignature().genericType.mapGenVarsTo(valueType, actual);
    Map<VarType, VarType> solved = new HashMap<>();
    for (Map.Entry<VarType, VarType> entry : hierarchy.entrySet()) {
      VarType actualValue = actual.get(entry.getKey());
      if (actualValue == null) {
        continue;
      }
      if (!unifyCastVariable(entry.getValue(), actualValue, solved)) {
        return null;
      }
    }
    return targetClass.getSignature().genericType.remap(solved);
  }

  /** Binds the type variables of {@code pattern} to the matching parts of {@code actual}. */
  private static boolean unifyCastVariable(VarType pattern, VarType actual, Map<VarType, VarType> solved) {
    if (pattern == null || actual == null) {
      return pattern == actual;
    }
    if (pattern.type == CodeType.GENVAR && pattern.arrayDim == 0
      && (!(pattern instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO)) {
      VarType key = pattern.resizeArrayDim(0);
      VarType existing = solved.get(key);
      if (existing != null) {
        return sameType(existing, actual);
      }
      solved.put(key, actual);
      return true;
    }
    if (pattern instanceof GenericType patternType && actual instanceof GenericType actualType
      && patternType.getWildcard() == GenericType.WILDCARD_NO
      && actualType.getWildcard() == GenericType.WILDCARD_NO
      && pattern.value != null && pattern.value.equals(actual.value)
      && patternType.getArguments().size() == actualType.getArguments().size()) {
      for (int i = 0; i < patternType.getArguments().size(); i++) {
        if (!unifyCastVariable(patternType.getArguments().get(i), actualType.getArguments().get(i), solved)) {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  /**
   * Whether a cast may name this instantiation: every type argument is recorded and nameable (an
   * unbounded wildcard is nameable, a capture or an out-of-scope variable is not), no argument is
   * a raw generic class, and no argument violates its declared bound.
   */
  public static boolean isNameableCastInstantiation(VarType type, Map<VarType, List<VarType>> named) {
    if (!(type instanceof GenericType generic) || generic.getWildcard() != GenericType.WILDCARD_NO
      || type.type != CodeType.OBJECT || type.arrayDim != 0 || type.value == null) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    if (cls == null || cls.getSignature() == null) {
      return false;
    }
    List<VarType> arguments = generic.getArguments();
    if (arguments.size() != cls.getSignature().fparameters.size()) {
      return false;
    }
    for (VarType argument : arguments) {
      if (!nameableCastArgument(argument, named)) {
        return false;
      }
    }
    return !hasRawTypeArgument(type) && !invalidGenericInstantiation(type);
  }

  /**
   * Whether the hoisted result cast may name this instantiation where it is printed. The type
   * must be a recorded, complete instantiation with every argument nameable; the only difference
   * from {@link #isNameableCastInstantiation} is that a type variable is looked up through a
   * nested lambda's source chain, whose synthetic static methods do not declare the enclosing
   * source method's parameters but whose text sits inside it.
   */
  private static boolean hoistCastInstantiationNameable(VarType type, Map<VarType, List<VarType>> named) {
    if (!(type instanceof GenericType generic) || generic.getWildcard() != GenericType.WILDCARD_NO
      || type.type != CodeType.OBJECT || type.arrayDim != 0 || type.value == null) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    if (cls == null || cls.getSignature() == null
      || generic.getArguments().size() != cls.getSignature().fparameters.size()) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (!hoistCastArgumentNameable(argument, named)) {
        return false;
      }
    }
    return !hasRawTypeArgument(type) && !invalidGenericInstantiation(type);
  }

  private static boolean hoistCastArgumentNameable(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null) {
      return true; // the unbounded wildcard
    }
    if (type.type == CodeType.GENVAR) {
      return hoistTypeVariableNameable(type.value, named);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (!hoistCastArgumentNameable(argument, named)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Whether a type variable is nameable at the print point. A lambda body is a synthetic static
   * method, but its source text sits in the enclosing method; a lambda nested in another lambda
   * chains through the synthetic methods, so the declaring source method can be several levels up.
   */
  private static boolean hoistTypeVariableNameable(String name, Map<VarType, List<VarType>> named) {
    if (name == null) {
      return false;
    }
    VarType variable = GenericType.parse("T" + name + ";");
    if (!named.containsKey(variable)) {
      return false;
    }
    if (Exprent.isTypeVariableNameable(variable, named)) {
      return true;
    }
    ClassNode current = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    if (current == null || current.type != ClassNode.Type.LAMBDA) {
      return false;
    }
    for (ClassNode node = current; node != null && node.parent != null; node = node.parent) {
      String enclosing = node.sourceEnclosingMethod != null ? node.sourceEnclosingMethod : node.enclosingMethod;
      if (enclosing == null || node.parent.getWrapper() == null) {
        continue;
      }
      MethodWrapper host = node.parent.getWrapper().getMethods().getWithKey(enclosing);
      if (host != null && host.methodStruct != null && host.methodStruct.getSignature() != null
        && host.methodStruct.getSignature().typeParameters.contains(name)) {
        return true;
      }
    }
    return false;
  }

  private static boolean nameableCastArgument(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null) {
      return true; // the unbounded wildcard
    }
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      if (type.type == CodeType.GENVAR) {
        return type.value != null
          && Exprent.isTypeVariableNameable(GenericType.parse("T" + type.value + ";"), named);
      }
      return nameableCastArguments(generic, named);
    }
    if (type.type == CodeType.GENVAR) {
      return Exprent.isTypeVariableNameable(type.resizeArrayDim(0), named);
    }
    return nameableCastArguments(type, named);
  }

  private static boolean nameableCastArguments(VarType type, Map<VarType, List<VarType>> named) {
    if (!(type instanceof GenericType generic)) {
      return true;
    }
    for (VarType argument : generic.getArguments()) {
      if (!nameableCastArgument(argument, named)) {
        return false;
      }
    }
    return true;
  }

  /** Whether an instantiation names only unbounded wildcards, the capture form no source wrote. */
  public static boolean isAllWildcardInstantiation(VarType type) {
    if (!(type instanceof GenericType generic) || generic.getArguments().isEmpty()) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument != null) {
        return false;
      }
    }
    return true;
  }

  /** Whether a printed cast to this instantiation erases to the same value's recorded type. */
  public static boolean castTargetValid(VarType candidate, VarType operandType) {
    if (candidate == null || operandType == null) {
      return true;
    }
    return !provablyInconvertible(candidate, operandType) && !parameterizedCastIllegal(candidate, operandType);
  }

  /** JLS 4.5 "provably distinct" for one position, limited to the shapes the printer produces. */
  private static boolean argumentProvablyDistinct(VarType target, VarType value) {
    if (target == null || value == null || target.type == CodeType.GENVAR || value.type == CodeType.GENVAR) {
      return false;
    }
    if (target instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    if (value instanceof GenericType wild && wild.getWildcard() != GenericType.WILDCARD_NO) {
      // A capture of ? extends B may only be cast to an instantiation below B; a supertype of
      // the bound (or an unrelated class) is provably distinct.
      if (wild.getWildcard() != GenericType.WILDCARD_EXTENDS || wild.value == null
        || target.isGeneric() || target.type != CodeType.OBJECT || target.value == null) {
        return false;
      }
      return !DecompilerContext.getStructContext().instanceOf(target.value, wild.value);
    }
    if (target.isGeneric() != value.isGeneric()) {
      return false;
    }
    if (target.isGeneric()) {
      return !((GenericType) target).equalsExact(value);
    }
    return target.type == CodeType.OBJECT && value.type == CodeType.OBJECT && !target.value.equals(value.value);
  }

  /** Whether a type argument names a generic class without its type arguments. */
  private static boolean hasRawTypeArgument(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument == null) {
        continue;
      }
      if (argument.type == CodeType.OBJECT && argument.arrayDim == 0 && !argument.isGeneric()
        && isGenericClass(argument.value)) {
        return true;
      }
      if (hasRawTypeArgument(argument)) {
        return true;
      }
    }
    return false;
  }

  /** Whether a class name denotes a class with type parameters, so a bare name is a raw type. */
  private static boolean isGenericClass(String internalName) {
    StructClass cls = DecompilerContext.getStructContext().getClass(internalName);
    if (cls != null && cls.getSignature() != null) {
      return !cls.getSignature().fparameters.isEmpty();
    }
    if (internalName.startsWith("java/") || internalName.startsWith("javax/")) {
      try {
        return Class.forName(internalName.replace('/', '.'), false, null).getTypeParameters().length > 0;
      }
      catch (Throwable ignored) {
        // Without the class there is no evidence that the name is raw.
      }
    }
    return false;
  }

  /** Whether the type names a type variable the enclosing source declares, at any depth. */
  private static boolean hasInScopeTypeVariable(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return named.containsKey(type);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (hasInScopeTypeVariable(argument, named)) {
          return true;
        }
      }
    }
    return false;
  }

  /** Whether a method-reference argument's inferred SAM return is an unnameable type variable. */
  private static boolean captureReturnedArgument(Exprent exprent) {
    if (!(exprent instanceof InvocationExprent invocation)) {
      return false;
    }
    Map<VarType, List<VarType>> named = exprent.getNamedGenerics();
    for (Exprent argument : invocation.getLstParameters()) {
      if (argument instanceof NewExprent lambda && lambda.isLambda() && lambda.isMethodReference()) {
        VarType produced = lambda.getFunctionalReturnType();
        if (produced != null && produced.type == CodeType.GENVAR
          && (!(produced instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO)
          && !named.containsKey(produced)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Whether a type variable can be written where the cast is printed. A class's own variables are
   * not nameable from a static member, and a variable of an enclosing class is not either.
   */
  private static boolean nameableVariable(String name) {
    MethodWrapper method = (MethodWrapper)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
    if (method == null || method.methodStruct == null) {
      return false;
    }
    GenericMethodDescriptor signature = method.methodStruct.getSignature();
    if (signature != null && signature.typeParameters.contains(name)) {
      return true;
    }
    return !method.methodStruct.hasModifier(CodeConstants.ACC_STATIC);
  }

  /** Whether the value's erasure can be converted to the target's: the same class, a subtype, or Object. */
  private static boolean castableToErasure(Exprent exprent, VarType target) {
    VarType value = exprent.getExprType();
    if (value == null || target.type != CodeType.OBJECT || target.arrayDim != 0 || target.value == null
      || value.type != CodeType.OBJECT || value.arrayDim != 0 || value.value == null) {
      return false;
    }
    if (value.value.equals(target.value) || "java/lang/Object".equals(value.value)) {
      return true;
    }
    StructContext context = DecompilerContext.getStructContext();
    return context != null && context.instanceOf(value.value, target.value);
  }

  /**
   * Whether the type is an instantiation with a `? super T` argument naming a type variable that is
   * in scope where the cast would be printed. A variable of the enclosing class is not nameable
   * from a static member, and printing it would not compile.
   */
  private static boolean lowerBoundedWildcardTarget(VarType type) {
    if (!(type instanceof GenericType generic) || generic.value == null) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument instanceof GenericType wildcard && wildcard.getWildcard() == GenericType.WILDCARD_SUPER
        && wildcard.type == CodeType.GENVAR && nameableVariable(wildcard.value)) {
        return true;
      }
    }
    return false;
  }

  /** A concrete target instantiated from a wildcard declaration: assignable only through a cast. */
  private static boolean needsCaptureCast(VarType target, VarType declared) {
    if (!(target instanceof GenericType concrete) || !(declared instanceof GenericType wild)) {
      return false;
    }
    if (concrete.value == null || !concrete.value.equals(wild.value)) {
      return false;
    }
    return !hasWildcard(concrete) && hasWildcard(wild);
  }

  private static boolean hasWildcard(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return false;
    }
    if (generic.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    for (VarType argument : generic.getArguments()) {
      // An unbound wildcard is a null argument.
      if (argument == null || hasWildcard(argument)) {
        return true;
      }
    }
    return false;
  }

  /** Whether some concrete type argument of a generic type is outside its formal bound. */
  private static boolean invalidGenericInstantiation(VarType type) {
    if (!(type instanceof GenericType generic) || generic.getArguments().isEmpty()) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    if (cls == null) {
      return false;
    }
    GenericClassDescriptor signature = cls.getSignature();
    if (signature == null) {
      return false;
    }
    List<VarType> arguments = generic.getArguments();
    for (int i = 0; i < arguments.size() && i < signature.fbounds.size(); i++) {
      VarType argument = arguments.get(i);
      if (argument == null || argument.type != CodeType.OBJECT || argument.value == null) {
        continue;
      }
      for (VarType bound : signature.fbounds.get(i)) {
        if (bound == null || bound.type != CodeType.OBJECT || bound.value == null) {
          continue;
        }
        if (bound.value.equals(argument.value)) {
          // T extends Comparable<T> cannot be instantiated with a wildcard: `Comparable<?>` is not
          // a type that satisfies its own bound.
          if (bound instanceof GenericType bounded && argument instanceof GenericType concrete
              && bounded.getArguments().stream().anyMatch(a -> a != null && a.type == CodeType.GENVAR)
              && concrete.getArguments().stream().anyMatch(a -> a == null || (a instanceof GenericType g
                  && g.getWildcard() != GenericType.WILDCARD_NO))) {
            return true;
          }
          continue;
        }
        if (!DecompilerContext.getStructContext().instanceOf(argument.value, bound.value)) {
          return true;
        }
      }
    }
    return false;
  }

  // (Obj)expr; -> (Obj<T>)expr;
  public static Exprent narrowGenericCastType(Exprent expr, VarType type) {
    if (type.isGeneric() && expr instanceof FunctionExprent && ((FunctionExprent)expr).getFuncType() == FunctionType.CAST) {
      FunctionExprent func = (FunctionExprent) expr;
      VarType funcType = func.getExprType();

      GenericType genType = (GenericType) type;
      if (funcType.value.equals(type.value) && !genType.getArguments().isEmpty()) {
        // Trying to cast to a generic type but the cast isn't generic- invalid!
        if (!funcType.isGeneric()) {
          // ...unless the type arguments cannot satisfy the bounds; the original's raw cast then
          // stays raw, which is also what javac needs.
          if (!invalidGenericInstantiation(type)) {
            ConstExprent cast = ((ConstExprent) func.getLstOperands().get(1));
            cast.setConstType(type);
          }
        } else if (genType.equalsExact(funcType) && !func.doesCast()) {
          // The cast's recorded target and the context target are the same type. A cast around
          // a value whose own source type is exactly that type is the redundant one javac
          // reports; keep the value bare and let its type stand.
          VarType valueType = func.getLstOperands().get(0).getInferredExprType(null);
          if (sameType(valueType, funcType)) {
            func.setCompilerCast(true);
          } else {
            func.setNeedsCast(true);
          }
        }
      }
    }

    return expr;
  }

  // Checks if two generic types should cast based on their type parameters.
  // If both the left and the right types are generics, compare the type parameters based on a set of rules to see if
  // the types are compatible. If a matching rule is identified, return and inform the type processor that the types
  // should cast.
  private static boolean doGenericTypesCast(Exprent ex, VarType left, VarType right) {
    Map<VarType, List<VarType>> named = ex.getNamedGenerics();
    if (left == null || right == null) {
      return false;
    }
    // A lambda argument is typed by its target: javac infers its parameter and return types from
    // the functional interface, so a cast around it is not evidence of a source cast and, when the
    // call's own type argument was inferred from a sibling argument, names the wrong type.
    if (ex instanceof NewExprent lambda && lambda.isLambda()) {
      return false;
    }
    // A cast is a source form the original wrote to make a call typecheck. Casts to a type whose
    // *direct* type argument is a wildcard (EntityType<? extends Mob>) are real and needed. An
    // invented one instead carries the wildcard one level deeper (App<Mu<? extends X>, T>), where
    // javac's inference already handles the argument and the cast can name an out-of-scope variable.
    if (left instanceof GenericType generic && generic.getWildcard() == GenericType.WILDCARD_NO
      && hasDeepWildcard(generic)) {
      return false;
    }

    if (left.isGeneric() && right.isGeneric()) {
      boolean contextFixed = contextIndependentValue(ex);
      if (shouldGenericTypesCast(named, left, right, contextFixed)) {
        return true;
      }

      GenericType leftGeneric = (GenericType) left;
      GenericType rightGeneric = (GenericType) right;

      if (leftGeneric.getArguments().size() != rightGeneric.getArguments().size()) {
        return false;
      }

      for (int i = 0; i < leftGeneric.getArguments().size(); i++) {
        VarType leftType = leftGeneric.getArguments().get(i);
        VarType rightType = rightGeneric.getArguments().get(i);
        if (rightType == null && leftType != null) {
          return true;
        }

        if (leftType != null) {
          if (shouldGenericTypesCast(named, leftType, rightType, contextFixed)) {
            return true;
          }
        }
      }
    }

    return plainClassToInvariantGeneric(left, right);
  }

  /** True when a wildcard sits below the type's direct arguments, not in them. */
  private static boolean hasDeepWildcard(GenericType type) {
    for (VarType argument : type.getArguments()) {
      if (!(argument instanceof GenericType generic)
        || generic.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      if (containsWildcard(generic)) {
        return true;
      }
    }
    return false;
  }

  private static boolean containsWildcard(GenericType type) {
    if (type.getWildcard() != GenericType.WILDCARD_NO) {
      return true;
    }
    for (VarType argument : type.getArguments()) {
      if (argument instanceof GenericType generic && containsWildcard(generic)) {
        return true;
      }
    }
    return false;
  }

  /**
   * A plain class assigned to a generic type: its supertype instantiation is recorded in its own
   * class file, and {@code class C implements Owner<Object>} is not an {@code Owner<T>} for an
   * unknown T, so the source made the assignment compile with a cast.
   */
  private static boolean plainClassToInvariantGeneric(VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || right.isGeneric()
      || right.type != CodeType.OBJECT) {
      return false;
    }
    VarType view = GenericType.getGenericSuperType(right, left);
    if (!(view instanceof GenericType genView) || !left.value.equals(genView.value)) {
      return false;
    }
    List<VarType> targetArgs = ((GenericType) left).getArguments();
    List<VarType> actualArgs = genView.getArguments();
    if (targetArgs.size() != actualArgs.size()) {
      return false;
    }
    for (int i = 0; i < targetArgs.size(); i++) {
      VarType targetArg = targetArgs.get(i);
      VarType actualArg = actualArgs.get(i);
      if (targetArg == null || actualArg == null) {
        continue;
      }
      if (targetArg instanceof GenericType genericArg && genericArg.getWildcard() != GenericType.WILDCARD_NO) {
        continue;
      }
      if (targetArg.type == CodeType.GENVAR && actualArg.type != CodeType.GENVAR && !targetArg.equals(actualArg)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the target and the value are instantiations of one generic class with a plain type
   * variable of this scope in the target and a different argument in the value at the same
   * position. The instantiations are invariant, so no assignment converts one into the other and
   * a source that compiled cast the value; the matching erasure makes the cast free.
   */
  private static boolean invariantTypeVariableMismatch(Map<VarType, List<VarType>> named,
                                                       VarType left, VarType right) {
    if (!(left instanceof GenericType target) || !(right instanceof GenericType value)
      || left.arrayDim != 0 || right.arrayDim != 0 || left.value == null
      || !left.value.equals(right.value)
      || target.getWildcard() != GenericType.WILDCARD_NO || value.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    List<VarType> targetArguments = target.getArguments();
    List<VarType> valueArguments = value.getArguments();
    if (targetArguments.size() != valueArguments.size()) {
      return false;
    }
    for (int i = 0; i < targetArguments.size(); i++) {
      VarType targetArgument = targetArguments.get(i);
      VarType valueArgument = valueArguments.get(i);
      if (plainTypeVariable(targetArgument) && named.containsKey(targetArgument)
        && valueArgument != null && !targetArgument.equals(valueArgument)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the type argument {@code target} is contained by the wildcard argument's {@code bound}:
   * the same type variable, a parameterization whose arguments are contained position by
   * position, or a value inside an upper-bounded wildcard's bound.
   */
  private static boolean boundContainsTarget(VarType bound, VarType target) {
    if (bound == null || target == null) {
      return bound == target; // an unbounded wildcard contains only itself
    }
    if (bound instanceof GenericType genericBound && genericBound.getWildcard() != GenericType.WILDCARD_NO) {
      VarType base = GenericType.withWildcard(genericBound, GenericType.WILDCARD_NO);
      return genericBound.getWildcard() == GenericType.WILDCARD_EXTENDS
        ? boundContainsTarget(base, target)
        : boundContainsTarget(target, base);
    }
    if (bound.type == CodeType.GENVAR) {
      return sameType(bound, target);
    }
    if (bound instanceof GenericType genericBound && target instanceof GenericType genericTarget
      && genericBound.getWildcard() == GenericType.WILDCARD_NO
      && genericTarget.getWildcard() == GenericType.WILDCARD_NO
      && genericBound.value != null && genericBound.value.equals(genericTarget.value)
      && genericBound.getArguments().size() == genericTarget.getArguments().size()) {
      for (int i = 0; i < genericBound.getArguments().size(); i++) {
        if (!boundContainsTarget(genericBound.getArguments().get(i), genericTarget.getArguments().get(i))) {
          return false;
        }
      }
      return true;
    }
    return sameType(bound, target);
  }

  /** Whether the type mentions a type variable at or below this position. */
  private static boolean mentionsGenericVariable(VarType type) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return true;
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        if (mentionsGenericVariable(argument)) {
          return true;
        }
      }
    }
    return false;
  }

  /** A type variable with no wildcard of its own (the variable itself, not {@code ? extends T}). */
  private static boolean plainTypeVariable(VarType type) {
    return type != null && type.type == CodeType.GENVAR
      && (!(type instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO);
  }

  /** An unbounded wildcard is a null argument; a bounded one carries its own wildcard type. */
  private static boolean isWildcardArgument(VarType type) {
    return type == null || (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO);
  }

  /**
   * A value whose type does not depend on the context it is printed in. A cast around a generic
   * call or a diamond is itself the context for its inference, so the source could not have
   * written one there: the call would have been inferred without the target and produced the
   * type the printer already sees. Only a variable, field, constant, or a conditional of them
   * is fixed by the class file alone.
   */
  public static boolean contextIndependentValue(Exprent exprent) {
    if (exprent instanceof VarExprent || exprent instanceof FieldExprent || exprent instanceof ConstExprent) {
      return true;
    }
    if (exprent instanceof FunctionExprent function && function.getFuncType() == FunctionType.TERNARY) {
      List<Exprent> operands = function.getLstOperands();
      return operands.size() == 3 && contextIndependentValue(operands.get(1)) && contextIndependentValue(operands.get(2));
    }
    return false;
  }

  /** A field qualifier the class file types without inference: this, a local, a field or a constant. */
  private static boolean contextIndependentQualifier(FieldExprent field) {
    Exprent qualifier = field.getInstance();
    return qualifier == null || contextIndependentValue(qualifier);
  }

  /**
   * Whether the target type names a type variable where the value's recorded type carries a
   * wildcard in the same invariant position. The variable must be in scope at the point of
   * printing, otherwise the cast would be illegal; a wildcard on the target side is fine
   * (X&lt;T&gt; is an X&lt;?&gt;), so only the target-variable/value-wildcard direction counts.
   */
  private static boolean invariantWildcardTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || !right.isGeneric()
      || !left.value.equals(right.value) || left.type != CodeType.OBJECT) {
      return false;
    }
    GenericType leftGeneric = (GenericType) left;
    GenericType rightGeneric = (GenericType) right;
    if (leftGeneric.getWildcard() != GenericType.WILDCARD_NO
      || rightGeneric.getWildcard() != GenericType.WILDCARD_NO
      || leftGeneric.getArguments().size() != rightGeneric.getArguments().size()) {
      return false;
    }
    for (int i = 0; i < leftGeneric.getArguments().size(); i++) {
      VarType targetArg = leftGeneric.getArguments().get(i);
      VarType valueArg = rightGeneric.getArguments().get(i);
      if (targetArg != null && targetArg.type == CodeType.GENVAR && named.containsKey(targetArg)
        && isWildcardArgument(valueArg)) {
        return true;
      }
      if (targetArg != null && valueArg != null && invariantWildcardTarget(named, targetArg, valueArg)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the value's recorded generic instantiation is a subclass of the target's generic class
   * whose recorded class signature, instantiated with the value's own arguments, puts a wildcard
   * where the target has a type variable in scope. Both sides are then different instantiations of
   * the same generic supertype in an invariant position, so no assignment converts one to the
   * other and a source that compiled cast the value to the target.
   */
  private static boolean wildcardSubtypeTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || !left.isGeneric() || !right.isGeneric()
      || left.value == null || right.value == null || left.value.equals(right.value)
      || left.arrayDim != 0 || right.arrayDim != 0) {
      return false;
    }
    if (((GenericType) left).getWildcard() != GenericType.WILDCARD_NO
      || ((GenericType) right).getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    StructClass derivedClass = DecompilerContext.getStructContext().getClass(right.value);
    StructClass targetClass = DecompilerContext.getStructContext().getClass(left.value);
    if (derivedClass == null || targetClass == null
      || derivedClass.getSignature() == null || targetClass.getSignature() == null) {
      return false;
    }
    // For each type parameter of the target class, the deriving class's own type parameter the
    // recorded hierarchy binds it to.
    Map<VarType, VarType> superMap = derivedClass.getAllGenerics().get(targetClass.qualifiedName);
    if (superMap == null) {
      return false;
    }
    List<String> targetParameters = targetClass.getSignature().fparameters;
    List<VarType> targetArguments = ((GenericType) left).getArguments();
    if (targetParameters.size() != targetArguments.size()) {
      return false;
    }
    // The value's instantiation of the deriving class's type parameters: an unbounded wildcard
    // argument is recorded as null, so the map can carry null values.
    Map<VarType, VarType> actual = new HashMap<>();
    derivedClass.getSignature().genericType.mapGenVarsTo((GenericType) right, actual);
    for (int i = 0; i < targetArguments.size(); i++) {
      VarType targetArgument = targetArguments.get(i);
      if (!plainTypeVariable(targetArgument) || !named.containsKey(targetArgument)) {
        continue;
      }
      VarType derivedVariable = superMap.get(GenericType.parse("T" + targetParameters.get(i) + ";"));
      if (derivedVariable == null || derivedVariable.type != CodeType.GENVAR || !actual.containsKey(derivedVariable)) {
        continue;
      }
      VarType derived = actual.get(derivedVariable);
      // A wildcard, or a different type variable of the enclosing source, in an invariant
      // position: neither is literally the target's variable, so the value does not assign and
      // the source cast it (Constant<I> returned as CubicSpline<R>).
      if (isWildcardArgument(derived)
        || plainTypeVariable(derived) && named.containsKey(derived) && !derived.equals(targetArgument)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the target type is an array whose element is a type variable of the enclosing source
   * while the value's array type is a different one. Arrays are covariant only over reifiable
   * element types, and no array whose element is not that same variable is a subtype of
   * {@code S[]}, so a source that compiled had to cast; the call's recorded signature (a field or
   * method signature, possibly on another class) proves the target is {@code S[]}. Only a value
   * whose erased array type is exactly {@code Object[]} is judged: the cast then erases to the
   * variable's unbounded erasure, so javac emits no checkcast for it.
   */
  private static boolean typeVariableArrayTarget(Map<VarType, List<VarType>> named, VarType left, VarType right) {
    if (left == null || right == null || left.arrayDim == 0 || left.arrayDim != right.arrayDim) {
      return false;
    }
    VarType leftBase = left.resizeArrayDim(0);
    VarType rightBase = right.resizeArrayDim(0);
    return leftBase.type == CodeType.GENVAR
      && named.containsKey(leftBase)
      && !leftBase.equals(rightBase)
      && rightBase.equals(VarType.VARTYPE_OBJECT);
  }

  /**
   * Whether a value of the recorded type {@code value} already fits the declared parameter type
   * {@code declared}, with the called method's own type variables instantiated by this argument.
   * A free variable binds to a proper (non-wildcard) argument inside its bound; a wildcard value
   * binds to its capture when the capture's upper bound lies within the variable's declared bound
   * and the call's result still fits the context target. Positions that cannot be judged (a
   * lower-bounded wildcard, a class with a different parameterization) reject.
   *
   * @param target the type the call's result is printed against, or null when unknown
   */
  public static boolean declaredTypeAccepts(VarType declared, VarType value,
                                            List<String> variables, Map<String, List<VarType>> bounds,
                                            Map<VarType, List<VarType>> named,
                                            VarType returnType, Map<String, VarType> bindings,
                                            VarType target) {
    return declaredTypeAccepts(declared, value, variables, bounds, named, returnType, bindings,
      Map.of(), VarType.VARTYPE_OBJECT, target);
  }

  /**
   * The form with the variables javac may re-infer at an input position. See
   * {@link #mergeableVariables}: a second occurrence of such a variable is accepted at another
   * instantiation when the target leaves the variable to inference.
   */
  public static boolean declaredTypeAccepts(VarType declared, VarType value,
                                            List<String> variables, Map<String, List<VarType>> bounds,
                                            Map<VarType, List<VarType>> named,
                                            VarType returnType, Map<String, VarType> bindings,
                                            Map<String, String> mergeable, VarType target) {
    return declaredTypeAccepts(declared, value, variables, bounds, named, returnType, bindings,
      mergeable, VarType.VARTYPE_OBJECT, target);
  }

  /**
   * The recursive form: {@code captureBound} is the upper bound of the class parameter whose
   * argument position the value occupies, which is the upper bound javac gives a wildcard's
   * capture there.
   */
  private static boolean declaredTypeAccepts(VarType declared, VarType value,
                                             List<String> variables, Map<String, List<VarType>> bounds,
                                             Map<VarType, List<VarType>> named,
                                             VarType returnType, Map<String, VarType> bindings,
                                             Map<String, String> mergeable,
                                             VarType captureBound, VarType target) {
    if (declared == null || declared.equals(VarType.VARTYPE_OBJECT)) {
      // An unbounded wildcard argument position, and Object, accept any value.
      return true;
    }
    if (value == null) {
      // An unbounded wildcard value instantiates nothing by itself. javac captures it with the
      // class parameter's upper bound; a free method variable binds to that capture when the
      // variable's declared bound accepts the capture's bound and the call's result still fits
      // the context. Every other position rejects.
      if (declared.type != CodeType.GENVAR || declared.arrayDim != 0
        || declared instanceof GenericType declaredWildcard
        && declaredWildcard.getWildcard() != GenericType.WILDCARD_NO
        || !variables.contains(declared.value) || bindings.containsKey(declared.value)) {
        return false;
      }
      VarType capture = captureBound == null ? VarType.VARTYPE_OBJECT : captureBound;
      if (!withinDeclaredBound(capture, declared.value, bounds, named)
        || !captureReturnFitsTarget(returnType, declared.value, capture, target, named)) {
        return false;
      }
      bindings.put(declared.value, null);
      return true;
    }
    if (declared.arrayDim > 0 || value.arrayDim > 0) {
      // An array position compares its element types; a variable inside the element instantiates
      // per element, not as the whole array.
      if (declared.arrayDim != value.arrayDim) {
        return false;
      }
      return declaredTypeAccepts(declared.resizeArrayDim(0), value.resizeArrayDim(0),
        variables, bounds, named, returnType, bindings, mergeable, captureBound, target);
    }
    if (declared instanceof GenericType declaredGeneric
      && declaredGeneric.getWildcard() != GenericType.WILDCARD_NO) {
      VarType base = GenericType.withWildcard(declaredGeneric, GenericType.WILDCARD_NO);
      if (declaredGeneric.getWildcard() == GenericType.WILDCARD_UNBOUND) {
        return true;
      }
      if (declaredGeneric.getWildcard() == GenericType.WILDCARD_SUPER) {
        // A lower-bounded position accepts no captured value.
        return false;
      }
      if (value instanceof GenericType valueGeneric
        && valueGeneric.getWildcard() != GenericType.WILDCARD_NO) {
        if (valueGeneric.getWildcard() != GenericType.WILDCARD_EXTENDS) {
          return false;
        }
        value = GenericType.withWildcard(valueGeneric, GenericType.WILDCARD_NO);
      }
      return declaredTypeAccepts(base, value, variables, bounds, named, returnType, bindings,
        mergeable, captureBound, target);
    }
    if (declared.type == CodeType.GENVAR) {
      String name = declared.value;
      if (variables.contains(name)) {
        if (bindings.containsKey(name)) {
          return mergeableAccepts(mergeable, name, bindings.get(name), value)
            || bindingCompatible(bindings.get(name), value, named);
        }
        boolean wildcard = value instanceof GenericType genericValue
          && genericValue.getWildcard() != GenericType.WILDCARD_NO;
        VarType bound = value;
        if (wildcard) {
          // The variable binds to the wildcard's capture. A bare return of the variable keeps the
          // binder by definition; otherwise the call's result must still fit the context with the
          // capture in place, which only a covariant or supertype position proves.
          boolean returnedBare = returnType instanceof GenericType returned
            && returned.getWildcard() == GenericType.WILDCARD_NO && returned.type == CodeType.GENVAR
            && name.equals(returned.value);
          VarType capture = value instanceof GenericType genericValue
            && genericValue.getWildcard() == GenericType.WILDCARD_EXTENDS
            ? GenericType.withWildcard(genericValue, GenericType.WILDCARD_NO) : VarType.VARTYPE_OBJECT;
          if (!returnedBare && !captureReturnFitsTarget(returnType, name, capture, target, named)) {
            return false;
          }
          bound = capture;
        }
        if (!withinDeclaredBound(bound, name, bounds, named)) {
          return false;
        }
        bindings.put(name, value);
        return true;
      }
      return sameType(declared, value);
    }
    if (!(declared instanceof GenericType declaredGeneric) || declaredGeneric.value == null) {
      if (sameType(declared, value)) {
        return true;
      }
      return declared.type == CodeType.OBJECT && value.type == CodeType.OBJECT
        && declared.value != null && value.value != null && declared.arrayDim == value.arrayDim
        && DecompilerContext.getStructContext().instanceOf(value.value, declared.value);
    }
    if (!(value instanceof GenericType valueGeneric)
      || valueGeneric.getWildcard() != GenericType.WILDCARD_NO
      || !declaredGeneric.value.equals(valueGeneric.value)
      || declaredGeneric.arrayDim != valueGeneric.arrayDim
      || declaredGeneric.getArguments().size() != valueGeneric.getArguments().size()) {
      return false;
    }
    for (int i = 0; i < declaredGeneric.getArguments().size(); i++) {
      if (!declaredTypeAccepts(declaredGeneric.getArguments().get(i), valueGeneric.getArguments().get(i),
        variables, bounds, named, returnType, bindings, mergeable,
        classParameterBound(declaredGeneric.value, i), target)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Whether the recorded target accepts javac's own inference of {@code variable} everywhere the
   * result type carries it. A target position that names a proper instantiation is what the
   * source's cast produced; an unbounded wildcard (also its null argument form), Object, or an
   * all-wildcard instantiation {@code G<?>} leaves the variable to inference.
   */
  public static boolean targetAcceptsReinference(VarType result, VarType target, String variable) {
    return result != null && target != null
      && acceptedTargetShape(result, target, variable) != null;
  }

  /** The shape the target accepts at this position, or null when it pins the variable. */
  private static @Nullable String acceptedTargetShape(VarType result, VarType target, String variable) {
    if (result == null) {
      return null;
    }
    if (result.arrayDim > 0 || target != null && target.arrayDim > 0) {
      if (target == null || result.arrayDim != target.arrayDim) {
        return null;
      }
      return acceptedTargetShape(result.resizeArrayDim(0), target.resizeArrayDim(0), variable);
    }
    if (result.type == CodeType.GENVAR && variable.equals(result.value)
      && (!(result instanceof GenericType generic) || generic.getWildcard() == GenericType.WILDCARD_NO)) {
      // The variable itself sits at this position: an unbounded target wildcard (also its null
      // argument form) or Object accepts whatever javac infers.
      return acceptsAnyType(target);
    }
    if (target == null) {
      return null;
    }
    if (result instanceof GenericType resultGeneric && target instanceof GenericType targetGeneric
      && resultGeneric.getWildcard() == GenericType.WILDCARD_NO
      && targetGeneric.getWildcard() == GenericType.WILDCARD_NO
      && resultGeneric.value != null && resultGeneric.value.equals(targetGeneric.value)
      && resultGeneric.getArguments().size() == targetGeneric.getArguments().size()) {
      String accepted = null;
      for (int i = 0; i < resultGeneric.getArguments().size(); i++) {
        VarType resultArgument = resultGeneric.getArguments().get(i);
        if (!mentionsTypeVariable(resultArgument, variable)) {
          continue;
        }
        String shape = acceptedTargetShape(resultArgument, targetGeneric.getArguments().get(i), variable);
        if (shape == null || accepted != null && !accepted.equals(shape)) {
          return null;
        }
        accepted = shape;
      }
      return accepted;
    }
    return null;
  }

  /**
   * The shape of a target position that accepts a re-inferred type: an unbounded wildcard (also
   * the null argument form), Object, or {@code G<?>} over an unbounded class.
   */
  private static @Nullable String acceptsAnyType(VarType target) {
    if (target == null || target.equals(VarType.VARTYPE_OBJECT)) {
      return "";
    }
    if (target instanceof GenericType generic) {
      if (generic.getWildcard() == GenericType.WILDCARD_UNBOUND) {
        return "";
      }
      if (generic.getWildcard() == GenericType.WILDCARD_NO && isAllWildcardInstantiation(generic)
        && generic.value != null && unboundedClassParameters(generic.value)) {
        return generic.value;
      }
    }
    return null;
  }

  /**
   * The type variables of the called method whose instantiation the call's recorded target does
   * not pin, mapped to the shape the target accepts there: the empty string for a position that
   * accepts any type (an unbounded wildcard or Object), or the class name of an all-wildcard
   * instantiation ({@code G<?>}). javac re-infers these from the argument list; a second argument
   * at another instantiation is then the common supertype javac itself computes, not a conversion
   * the source had to cast. A variable the result does not carry is excluded: another argument may
   * have bound it invariantly, and the target proves nothing about re-inferring it.
   */
  public static Map<String, String> mergeableVariables(GenericMethodDescriptor signature, VarType target) {
    if (signature == null || signature.typeParameters.isEmpty() || signature.returnType == null
      || target == null) {
      return Map.of();
    }
    Map<String, String> result = new HashMap<>();
    for (String variable : signature.typeParameters) {
      if (!mentionsTypeVariable(signature.returnType, variable)) {
        // The result does not carry it: another argument may bind it invariantly, and the target
        // proves nothing about whether javac can re-infer it from a common supertype.
        continue;
      }
      String shape = acceptedTargetShape(signature.returnType, target, variable);
      if (shape != null) {
        result.put(variable, shape);
      }
    }
    return result;
  }

  /** Whether a second binding may replace the first at a position the target leaves open. */
  private static boolean mergeableAccepts(Map<String, String> mergeable, String name, VarType bound,
                                          VarType value) {
    String shape = mergeable == null ? null : mergeable.get(name);
    if (shape == null) {
      return false;
    }
    if (shape.isEmpty()) {
      return true;
    }
    // The target accepts G<?>: two instantiations of that same class have a common supertype
    // (G<? extends lub>) the target accepts.
    return isInstantiationOf(bound, shape) && isInstantiationOf(value, shape);
  }

  private static boolean isInstantiationOf(VarType type, String className) {
    return type instanceof GenericType generic && generic.getWildcard() == GenericType.WILDCARD_NO
      && generic.type == CodeType.OBJECT && className.equals(generic.value)
      && !generic.getArguments().isEmpty();
  }

  /**
   * The first declared bound of the class's formal parameter at {@code index}. A wildcard value
   * at that position captures with this upper bound: {@code ParticleType<?>} is a
   * {@code ParticleType<capture of ? extends ParticleOptions>} because the class parameter is
   * bounded there. An unknown class or parameter yields Object.
   */
  private static VarType classParameterBound(String className, int index) {
    if (className == null || index < 0) {
      return VarType.VARTYPE_OBJECT;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null || cls.getSignature() == null
      || index >= cls.getSignature().fparameters.size()) {
      return VarType.VARTYPE_OBJECT;
    }
    List<VarType> classBounds = index < cls.getSignature().fbounds.size()
      ? cls.getSignature().fbounds.get(index) : null;
    if (classBounds == null || classBounds.isEmpty() || classBounds.get(0) == null) {
      return VarType.VARTYPE_OBJECT;
    }
    return classBounds.get(0);
  }

  private static boolean mentionsTypeVariable(VarType type, String variable) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return variable.equals(type.value);
    }
    if (type instanceof GenericType generic) {
      if (generic.getParent() != null && mentionsTypeVariable(generic.getParent(), variable)) {
        return true;
      }
      for (VarType argument : generic.getArguments()) {
        if (mentionsTypeVariable(argument, variable)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Whether a call whose return type names {@code variable} still fits the context target when
   * javac binds that variable to a wildcard's capture. The capture is a fresh type variable whose
   * upper bound is {@code captureBound}: it is assignable to a target position only through that
   * bound - a covariant wildcard or a plain supertype position - never through an invariant one,
   * where an unknown capture is not literally the target's type argument. A return type that does
   * not name the variable is unaffected by the binding.
   */
  private static boolean captureReturnFitsTarget(VarType returnType, String variable, VarType captureBound,
                                                 VarType target, Map<VarType, List<VarType>> named) {
    if (!mentionsTypeVariable(returnType, variable)) {
      return true;
    }
    if (target == null || target.equals(VarType.VARTYPE_VOID)) {
      return false;
    }
    return captureFitsTarget(returnType, target, variable, captureBound, named);
  }

  private static boolean captureFitsTarget(VarType returnType, VarType target, String variable,
                                           VarType captureBound, Map<VarType, List<VarType>> named) {
    if (!mentionsTypeVariable(returnType, variable)) {
      return true;
    }
    if (target == null) {
      return false;
    }
    if (target.equals(VarType.VARTYPE_OBJECT)) {
      return true;
    }
    if (target instanceof GenericType targetGeneric && targetGeneric.getWildcard() != GenericType.WILDCARD_NO) {
      if (targetGeneric.getWildcard() != GenericType.WILDCARD_EXTENDS) {
        // A lower bound asks for a supertype of a named type; an unknown capture proves nothing.
        return false;
      }
      target = GenericType.withWildcard(targetGeneric, GenericType.WILDCARD_NO);
    }
    if (returnType.arrayDim > 0 || target.arrayDim > 0) {
      return returnType.arrayDim == target.arrayDim
        && captureFitsTarget(returnType.resizeArrayDim(0), target.resizeArrayDim(0), variable, captureBound, named);
    }
    if (returnType.type == CodeType.GENVAR) {
      // The return type is the capture itself: it fits through the capture's upper bound.
      return valueAssignableTo(captureBound, target, named);
    }
    if (!(returnType instanceof GenericType returnGeneric) || !(target instanceof GenericType targetGeneric)
      || returnGeneric.value == null || !returnGeneric.value.equals(targetGeneric.value)) {
      return false;
    }
    List<VarType> returnArguments = returnGeneric.getArguments();
    List<VarType> targetArguments = targetGeneric.getArguments();
    if (returnArguments.isEmpty() || targetArguments.isEmpty()) {
      return returnArguments.isEmpty() || targetArguments.isEmpty();
    }
    if (returnArguments.size() != targetArguments.size()) {
      return false;
    }
    for (int i = 0; i < returnArguments.size(); i++) {
      if (!mentionsTypeVariable(returnArguments.get(i), variable)) {
        continue;
      }
      VarType wanted = targetArguments.get(i);
      if (wanted == null) {
        // An unbounded wildcard position accepts any type.
        continue;
      }
      int wantedWildcard = wanted instanceof GenericType wantedGeneric
        ? wantedGeneric.getWildcard() : GenericType.WILDCARD_NO;
      if (wantedWildcard == GenericType.WILDCARD_EXTENDS) {
        if (!captureFitsTarget(returnArguments.get(i),
          GenericType.withWildcard(wanted, GenericType.WILDCARD_NO), variable, captureBound, named)) {
          return false;
        }
      } else {
        // An invariant position, or a lower bound, never accepts an unknown capture.
        return false;
      }
    }
    return true;
  }

  /** Whether {@code value} is assignable to {@code limit}, generic instantiations included. */
  private static boolean valueAssignableTo(VarType value, VarType limit, Map<VarType, List<VarType>> named) {
    if (value == null) {
      return false;
    }
    if (limit == null) {
      return true;
    }
    return GenericType.isAssignable(value, limit, named);
  }

  /**
   * Whether a second occurrence of an already bound variable is compatible with the first: the
   * same type, a type variable on either side whose recorded bounds contain the other, or a
   * wildcard whose bound is the other.
   */
  private static boolean bindingCompatible(VarType binding, VarType value, Map<VarType, List<VarType>> named) {
    if (sameType(binding, value)) {
      return true;
    }
    if (binding == null || value == null) {
      return false;
    }
    if (binding instanceof GenericType genericBinding && genericBinding.getWildcard() != GenericType.WILDCARD_NO) {
      VarType bound = genericBinding.getWildcard() == GenericType.WILDCARD_EXTENDS
        ? GenericType.withWildcard(genericBinding, GenericType.WILDCARD_NO) : VarType.VARTYPE_OBJECT;
      return bindingCompatible(bound, value, named);
    }
    if (value instanceof GenericType genericValue && genericValue.getWildcard() != GenericType.WILDCARD_NO) {
      VarType bound = genericValue.getWildcard() == GenericType.WILDCARD_EXTENDS
        ? GenericType.withWildcard(genericValue, GenericType.WILDCARD_NO) : VarType.VARTYPE_OBJECT;
      return bindingCompatible(binding, bound, named);
    }
    if (value.type == CodeType.GENVAR) {
      List<VarType> limits = named.get(value);
      if (limits != null) {
        for (VarType limit : limits) {
          if (limit != null && sameType(limit, binding)) {
            return true;
          }
        }
      }
    }
    if (binding.type == CodeType.GENVAR) {
      List<VarType> limits = named.get(binding);
      if (limits != null) {
        for (VarType limit : limits) {
          if (limit != null && sameType(limit, value)) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Whether the printer's own substitution for a bound variable can stand beside the binding the
   * argument implies. A variable binding is re-inferred by javac and agrees with anything; a
   * proper binding agrees with the same type or Object; the one conflict javac cannot resolve is
   * a proper value the rest of the call needs at another type.
   */
  public static boolean substitutionCompatible(VarType binding, VarType substituted) {
    if (sameType(binding, substituted)) {
      return true;
    }
    if (binding == null || substituted == null) {
      return true;
    }
    if (binding instanceof GenericType genericBinding && genericBinding.getWildcard() != GenericType.WILDCARD_NO) {
      VarType bound = genericBinding.getWildcard() == GenericType.WILDCARD_EXTENDS
        ? GenericType.withWildcard(genericBinding, GenericType.WILDCARD_NO) : VarType.VARTYPE_OBJECT;
      return substitutionCompatible(bound, substituted);
    }
    if (binding.type == CodeType.GENVAR) {
      // javac re-infers the variable from this argument; the substitution is the printer's guess.
      return true;
    }
    // A proper value fixes the variable exactly: the call's result is an instantiation with that
    // argument, and the context that asked for another one does not accept a subtype of it.
    return substituted.equals(VarType.VARTYPE_OBJECT);
  }

  private static boolean withinDeclaredBound(VarType value, String variable, Map<String, List<VarType>> bounds,
                                             Map<VarType, List<VarType>> named) {
    List<VarType> limits = bounds.get(variable);
    if (limits == null || limits.isEmpty()) {
      return true;
    }
    for (VarType limit : limits) {
      if (limit == null || limit.equals(VarType.VARTYPE_OBJECT)) {
        return true;
      }
      if (sameType(value, limit)) {
        return true;
      }
      if (value != null && value.type == CodeType.OBJECT && limit.type == CodeType.OBJECT
        && value.value != null && limit.value != null && value.arrayDim == limit.arrayDim
        && DecompilerContext.getStructContext().instanceOf(value.value, limit.value)) {
        return true;
      }
      // A value that is itself a type variable of the caller satisfies the bound through its own
      // recorded bounds: each of them names the variable's upper limits at the call site.
      if (value != null && value.type == CodeType.GENVAR) {
        List<VarType> valueBounds = named.get(value);
        if (valueBounds != null) {
          for (VarType valueBound : valueBounds) {
            if (valueBound != null && sameType(valueBound, limit)) {
              return true;
            }
          }
        }
      }
    }
    return false;
  }

  private static boolean shouldGenericTypesCast(Map<VarType, List<VarType>> named, VarType leftType, VarType rightType,
                                                boolean contextFixed) {
    if (leftType.isGeneric()) {
      GenericType genLeft = (GenericType) leftType;
      if (rightType.isGeneric()) {
        GenericType genRight = (GenericType) rightType;

        if (leftType.higherEqualInLatticeThan(rightType)) {
          // Casting Clazz<?> to Clazz<T> or Clazz<Concrete>
          if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) &&
            genRight.getWildcard() == GenericType.WILDCARD_SUPER) {

            boolean ok = true;
            if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS) {
              // Equals, ignoring wildcards
              if (!genLeft.getArguments().isEmpty() && !genRight.getArguments().isEmpty() &&
                leftType.equals(rightType)) {
                ok = false;
              }
            }

            if (ok) {
              return true;
            }
          }
        } else {
          if (genLeft.getWildcard() == GenericType.WILDCARD_EXTENDS && genRight.getWildcard() == GenericType.WILDCARD_SUPER) {
            return true;
          }
          // Trying to cast two independent generics to each other? Check if they're both the base generic type (i.e. Object)
          // and force a cast if so.
          if (leftType.type == CodeType.GENVAR && rightType.type == CodeType.GENVAR
            && genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getWildcard() == GenericType.WILDCARD_NO) {

            if (named.containsKey(leftType) && named.containsKey(rightType) && named.get(leftType).contains(VarType.VARTYPE_OBJECT) && named.get(rightType).contains(VarType.VARTYPE_OBJECT)) {
              return true;
            }
          }
        }

        if ((genLeft.getWildcard() == GenericType.WILDCARD_NO || genLeft.getWildcard() == GenericType.WILDCARD_SUPER) &&
          genRight.getWildcard() == GenericType.WILDCARD_EXTENDS) {
          return true;
        }

        // Recurse on the type
        // Notably, *only* recurse if the current wildcard types are the same- otherwise we may run into incorrect casting behavior
        if (genLeft.getArguments().size() != genRight.getArguments().size()) {
          return false;
        }

        if (genLeft.getWildcard() == genRight.getWildcard()) {
          // Arguments of the same generic class are invariant positions: two instantiations are
          // the same type only when each argument is literally the same. A type variable on one
          // side and a different type on the other therefore never assigns across, and the source
          // made it compile with a cast.
          boolean invariant = leftType.value.equals(rightType.value);
          for (int i = 0; i < genLeft.getArguments().size(); i++) {
            VarType lt = genLeft.getArguments().get(i);
            VarType rt = genRight.getArguments().get(i);
            // Subset of Type<?> -> Type<T> check: Only check for genvars. If T is concrete, then don't force casting.
            if (rt == null && lt != null && lt.type == CodeType.GENVAR) {
              return true;
            }
            if (invariant && lt != null && rt != null
              && ((lt.type == CodeType.GENVAR && rt.type != CodeType.GENVAR && !rt.isGeneric())
                || (rt.type == CodeType.GENVAR && lt.type != CodeType.GENVAR && !lt.isGeneric()))) {
              return true;
            }
            // Two different type variables are different types even when one is a subtype of the
            // other: invariance never assigns X<A> to X<B>, so a source that did it cast, and the
            // target's variable must be nameable where the cast is printed. Only a value whose type
            // the class file fixes without context is cast; an argument list or a method reference
            // is inferred from the cast itself, so the source need not have written one. A bounded
            // wildcard of a variable (? extends B) is not the variable itself - Class<T> does
            // assign to Class<? extends B> - so both arguments must be plain variables.
            if (invariant && contextFixed && plainTypeVariable(lt) && plainTypeVariable(rt)
              && !lt.equals(rt) && named.containsKey(lt)) {
              return true;
            }

            if (lt != null && rt != null) {
              if (shouldGenericTypesCast(named, lt, rt, contextFixed)) {
                return true;
              }
            }
          }
        }
      } else {
        // Right is not generic
        // Check for casting a concrete rightType to a specific left generic
        // e.g. (List<T>)list where 'list' is List<Object>
        if (genLeft.getWildcard() == GenericType.WILDCARD_NO && genLeft.getArguments().isEmpty()) {
          return true;
        }
      }
    }

    return false;
  }

  private static boolean isIntConstant(Exprent exprent) {
    if (exprent instanceof ConstExprent) {
      switch (((ConstExprent)exprent).getConstType().type) {
        case BYTE:
        case BYTECHAR:
        case SHORT:
        case SHORTCHAR:
        case INT:
          return true;
      }
    }

    return false;
  }

  private static boolean isNarrowedIntType(VarType type) {
    return VarType.VARTYPE_INT.higherInLatticeThan(type) ||
           type.equals(VarType.VARTYPE_BYTE_OBJ) || type.equals(VarType.VARTYPE_SHORT_OBJ);
  }

  private static boolean lambdaNeedsCast(VarType left, NewExprent exprent) {
    // The invokedynamic names the interface javac built the lambda for, and it comes from the
    // target itself: when it is not the expected type, the source must have cast to it, or javac
    // would have built the lambda for the expected type instead.
    return exprent.isLambda() || exprent.isMethodReference();
  }

  /** The single abstract method that makes {@code cls} a functional interface, or null. */
  public static StructMethod functionalMethod(StructClass cls) {
    if (!cls.hasModifier(CodeConstants.ACC_INTERFACE)) {
      return null;
    }
    StructMethod found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!method.hasModifier(CodeConstants.ACC_ABSTRACT) || method.hasModifier(CodeConstants.ACC_STATIC)) {
        continue;
      }
      // Redeclaring an Object method is not an abstract method for functional-interface purposes.
      String name = method.getName();
      String desc = method.getDescriptor();
      if ((name.equals("equals") && desc.equals("(Ljava/lang/Object;)Z"))
          || (name.equals("hashCode") && desc.equals("()I"))
          || (name.equals("toString") && desc.equals("()Ljava/lang/String;"))) {
        continue;
      }
      if (found != null) {
        return null;
      }
      found = method;
    }
    return found;
  }

  private static boolean isFunctionalInterface(StructClass cls) {
    return functionalMethod(cls) != null;
  }
}
