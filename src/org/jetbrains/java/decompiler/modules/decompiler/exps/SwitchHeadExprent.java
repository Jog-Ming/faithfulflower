/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

public class SwitchHeadExprent extends Exprent {

  private Exprent value;
  private List<List<Exprent>> caseValues = new ArrayList<>();

  public SwitchHeadExprent(Exprent value, BitSet bytecodeOffsets) {
    super(Type.SWITCH_HEAD);
    this.value = value;

    addBytecodeOffsets(bytecodeOffsets);
  }

  @Override
  public Exprent copy() {
    SwitchHeadExprent swExpr = new SwitchHeadExprent(value.copy(), bytecode);

    List<List<Exprent>> lstCaseValues = new ArrayList<>();
    for (List<Exprent> lst : caseValues) {
      lstCaseValues.add(new ArrayList<>(lst));
    }
    swExpr.setCaseValues(lstCaseValues);

    return swExpr;
  }

  @Override
  public VarType getExprType() {
    return value.getExprType();
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    VarType valType = value.getExprType();
    for (List<Exprent> lst : caseValues) {
      for (Exprent expr : lst) {
        if (expr != null) {
          // TODO: refactor to PatternExprent
          VarType caseType = expr instanceof FunctionExprent && ((FunctionExprent) expr).getLstOperands().size() == 3
            ? ((FunctionExprent) expr).getLstOperands().get(1).getExprType()
            : expr.getExprType();
          if (!caseType.equals(valType)) {
            if (valType == null) {
              ValidationHelper.validateTrue(false, "Couldn't generate a valid merged switch set!");
              // TODO: should this add a bound of unknown to value?
              return result;
//              throw new IllegalStateException("Invalid switch case set: " + caseValues + " for selector of type " + value.getExprType());
            }
            // allow coercion of primitive -> boxes [see TestSwitchPatternMatching18]
            // e.g. `switch(o) { case 40 -> ...; case Integer i -> ...; }`
            // FIXME: still isn't right?
            VarType unboxed = VarType.UNBOXING_TYPES.get(valType);
            if (unboxed != null && unboxed.higherEqualInLatticeThan(caseType)) {
              continue;
            }
            valType = VarType.join(caseType, valType);
            if (valType != null) {
              result.addExprLowerBound(value, valType);
            }
          }
        }
      }
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    lst.add(value);
    return lst;
  }

  @Override
  public TextBuffer toJava(int indent) {
    Exprent printed = value;
    if (value instanceof FunctionExprent cast && cast.getFuncType() == FunctionType.CAST
      && cast.getLstOperands().size() == 2 && labelsProveSelectorType(cast.getLstOperands().get(1).getExprType())) {
      // The labels alone require the selector's type, so the source wrote the selector bare and
      // the recorded checkcast is the erasure boundary's: print its operand.
      printed = cast.getLstOperands().get(0);
    }
    TextBuffer buf = printed.toJava(indent).enclose("switch (", ")");
    buf.addStartBytecodeMapping(bytecode);
    return buf;
  }

  /**
   * Whether every case label forces the selector's type to the cast's class: enum constants of
   * that class, string constants, or patterns of that class or a subtype. A `case null` or a
   * label of another shape leaves the cast in place.
   */
  private boolean labelsProveSelectorType(VarType target) {
    if (target == null || target.type != CodeType.OBJECT || target.arrayDim != 0 || target.value == null) {
      return false;
    }
    boolean any = false;
    for (List<Exprent> values : caseValues) {
      if (values == null) {
        continue;
      }
      for (Exprent label : values) {
        if (label == null) {
          continue;
        }
        if (label instanceof FieldExprent field) {
          if (!field.isStatic() || !target.value.equals(field.getClassname())) {
            return false;
          }
        } else if (label instanceof ConstExprent constant) {
          VarType type = constant.getConstType();
          if (type == null || type.type != CodeType.OBJECT || !"java/lang/String".equals(type.value)) {
            return false;
          }
        } else if (label instanceof FunctionExprent pattern && pattern.getFuncType() == FunctionType.INSTANCEOF
          && pattern.getLstOperands().size() == 3) {
          VarType patternType = pattern.getLstOperands().get(1).getExprType();
          if (patternType == null || patternType.value == null
            || !DecompilerContext.getStructContext().instanceOf(patternType.value, target.value)) {
            return false;
          }
        } else {
          return false;
        }
        any = true;
      }
    }
    return any;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == value) {
      value = newExpr;
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    }

    if (!(o instanceof SwitchHeadExprent)) {
      return false;
    }

    SwitchHeadExprent sw = (SwitchHeadExprent)o;
    return InterpreterUtil.equalObjects(value, sw.getValue());
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    if (caseValues != null && !caseValues.isEmpty()) {
      for (List<Exprent> l : caseValues) {
        if (l != null && !l.isEmpty()) {
          for (Exprent e : l) {
            if (e != null)
              e.getBytecodeRange(values);
          }
        }
      }
    }
    measureBytecode(values, value);
    measureBytecode(values);
  }

  public Exprent getValue() {
    return value;
  }

  public void setValue(Exprent value) {
    this.value = value;
  }

  public List<List<Exprent>> getCaseValues() {
    return caseValues;
  }

  public void setCaseValues(List<List<Exprent>> caseValues) {
    this.caseValues = caseValues;
  }
}
