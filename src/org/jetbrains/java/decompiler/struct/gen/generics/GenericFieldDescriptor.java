// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.gen.generics;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;

public class GenericFieldDescriptor {
  public VarType type;

  public GenericFieldDescriptor(VarType type) {
    this.type = type;
  }

  public void verifyType(GenericClassDescriptor containingClassGenerics, VarType realType) {
    if (containingClassGenerics == null) {
//      DecompilerContext.getLogger().writeMessage("Class generics were not found, verifying type loosely", IFernflowerLogger.Severity.INFO);
      verifyLoosely(realType);
      return;
    }

    GenericsChecker checker = containingClassGenerics.getChecker();

    if (!checker.isProperlyBounded(type, realType)) {
      // A class file's descriptor is the erasure of its signature by construction. When the
      // signature names the very class the descriptor does, the lattice check compared a
      // parameterized type with its raw form and rejected it (a nested generic type's own type
      // parameter is the usual case), but the erasure equality proves the signature describes
      // this field. Falling back to the descriptor would print an erased type, which never
      // reproduces the original.
      if (type.type == CodeType.OBJECT && realType.type == CodeType.OBJECT
          && type.arrayDim == realType.arrayDim && type.value != null
          && type.value.equals(realType.value)) {
        return;
      }
      DecompilerContext.getLogger().writeMessage("Mismatched field signature, expected: " + realType.value + ", actual: " + type.value, IFernflowerLogger.Severity.WARN);
      type = realType;
    }
  }

  /** Whether {@code descriptor} is the erasure of {@code signature} (JVM-mandated for a field). */
  private static boolean sameErasure(VarType signature, VarType descriptor) {
    return signature.type == CodeType.OBJECT && descriptor.type == CodeType.OBJECT
      && signature.arrayDim == descriptor.arrayDim && signature.value != null
      && signature.value.equals(descriptor.value);
  }

  //FIXME this is necessary because some places don't have other signature information,
  // which prevents the ability to check class- or method-provided generic types
  public void verifyLoosely(VarType actualType) {
    if (actualType.higherEqualInLatticeThan(type)) {
      return;
    }

    if (type.type == CodeType.GENVAR) {
      return; // Impossible to verify
    }

    // The untyped check cannot judge a parameterization against its own raw erasure either; the
    // descriptor equals that erasure for every valid class file, so the signature stays.
    if (sameErasure(type, actualType)) {
      return;
    }

    DecompilerContext.getLogger().writeMessage("Mismatched field signature, expected: " + type.value + ", actual: " + actualType.value, IFernflowerLogger.Severity.WARN);
    type = actualType;
  }
}