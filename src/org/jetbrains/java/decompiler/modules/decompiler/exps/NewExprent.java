// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.VarMapHolder;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DummyExitStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.CheckTypesResult;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructTypeAnnotationAttribute;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericClassDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.InterpreterUtil;
import org.jetbrains.java.decompiler.util.Key;
import org.jetbrains.java.decompiler.util.collections.ListStack;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.io.IOException;
import java.util.*;

public class NewExprent extends Exprent {
  private InvocationExprent constructor;
  private final VarType newType;
  private final List<Exprent> lstDims;
  private List<Exprent> lstArrayElements = new ArrayList<>();
  private boolean directArrayInit;
  private boolean isVarArgParam;
  private boolean anonymous;
  private boolean lambda;
  private boolean methodReference = false;
  // Printed as the receiver of a call or field access: a receiver has no target type.
  private boolean isQualifier;

  private boolean enumConst;
  // The component of the context target of a generic array creation (`X<A>[]` from a field or
  // method signature). The array-creating instruction only names the erased class.
  private VarType arrayComponentTarget;
  private List<VarType> genericArgs = new ArrayList<>();
  private VarType inferredLambdaType = null;
  // Set when the lambda's interface type came from the wildcard form of the called method's
  // parameter type rather than from resolved arguments; only an in-scope type variable return
  // is used from such a target.
  private boolean wildcardTargetLambda = false;
  // The call site's recorded target names a capture at a SAM position instead of a type the
  // source could write. An identity parameter (the parameter and the return are one variable)
  // must then stay untyped, or the source's own cast, which guides the inference, is lost.
  private boolean functionalParameterCaptured = true;
  // Type arguments the class file proved for a constructor call whose diamond javac would
  // otherwise close on a narrower type than the recorded method reference needs.
  private List<VarType> forcedConstructorArgs;
  // The recovered arguments are subtypes of what the expected type needs at an invariant
  // position: only a diamond can let javac infer the expected arguments from the target.
  private boolean targetedDiamond;
  // A diamond whose recorded target is a parameterized supertype: the arguments implied by
  // that supertype's instantiation are the ones the source wrote on the constructor.
  private List<VarType> impliedConstructorArgs;
  // The context target of a creation that has no target type of its own (a field initializer,
  // a return value, a local's initializer). javac types such an expression from that target;
  // when the target fixes every type parameter of the created class, the source wrote the
  // diamond rather than the raw type the recovered argument list leaves behind.
  private VarType expectedCreationType;
  // The created class's own type arguments as that target fixes them; a null entry is the
  // unbounded wildcard.
  private List<VarType> expectedCreationArgs;

  public NewExprent(VarType newType, ListStack<Exprent> stack, int arrayDim, BitSet bytecodeOffsets) {
    this(newType, getDimensions(arrayDim, stack), bytecodeOffsets);
  }

  public NewExprent(VarType newType, List<Exprent> lstDims, BitSet bytecodeOffsets) {
    super(Type.NEW);
    this.newType = newType;
    this.lstDims = lstDims;

    anonymous = false;
    lambda = false;
    if (newType.type == CodeType.OBJECT && newType.arrayDim == 0) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
      if (node != null && (node.type == ClassNode.Type.ANONYMOUS || node.type == ClassNode.Type.LAMBDA)) {
        anonymous = true;
        if (node.type == ClassNode.Type.LAMBDA) {
          lambda = true;
          methodReference = node.lambdaInformation.is_method_reference;
        }
      }
    }

    addBytecodeOffsets(bytecodeOffsets);
  }

  private static List<Exprent> getDimensions(int arrayDim, ListStack<Exprent> stack) {
    List<Exprent> lstDims = new ArrayList<>();
    for (int i = 0; i < arrayDim; i++) {
      lstDims.add(0, stack.pop());
    }
    return lstDims;
  }

  @Override
  public VarType getExprType() {
    return anonymous ? DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value).anonymousClassType : newType;
  }

  @Override
  public VarType getInferredExprType(VarType upperBound) {
    genericArgs.clear();
    if (!lambda && newType.type == CodeType.OBJECT) {
      StructClass node = DecompilerContext.getStructContext().getClass(newType.value);
      recordExpectedCreationType(node == null ? null : node.getSignature(), upperBound);

      if (node != null && node.getSignature() != null) {
        if (newType.arrayDim > 0) {
          // The context records the instantiation the source wrote: `X<A>[]` from a field or
          // method signature, while the creation's own instruction names only the erased class.
          // A source can only write the all-wildcard form `new X<?>[]`, so the recorded target
          // also decides whether the value needs a cast to it.
          if (recordArrayComponent(upperBound)) {
            return printedArrayComponent().resizeArrayDim(newType.arrayDim);
          }
          // The array's component class is generic and the class file records it erased, but
          // every element's own recorded instantiation agrees: a varargs array of
          // `Pair.of(...)` calls is exactly `Pair<Item, ResourceKey<Pattern>>[]`, and the call
          // and the lambda that receives it are typed from it.
          VarType inferred = genericArrayComponent();
          if (inferred != null) {
            return inferred.resizeArrayDim(newType.arrayDim);
          }
        }
        if (anonymous) {
          if (VarType.VARTYPE_OBJECT.equals(node.getSignature().superclass) && !node.getSignature().superinterfaces.isEmpty()) {
            return node.getSignature().superinterfaces.get(0);
          }
          return node.getSignature().superclass;
        }
        else if (newType.arrayDim == 0 && !node.getSignature().fparameters.isEmpty()) {
          GenericClassDescriptor sig = node.getSignature();
          if (constructor != null) {
            // The recorded target is the instantiation javac inferred for a diamond; give it
            // to the constructor so its arguments are typed against the same parameter types.
            constructor.setCreationClassArgs(expectedCreationArgs);
            InvocationExprent.enterPoly();
            VarType ret;
            try {
              ret = constructor.getInferredExprType(upperBound);
            } finally {
              InvocationExprent.exitPoly();
            }
            if (expectsWiderArguments(upperBound)) {
              targetedDiamond = true;
            }
            List<VarType> recovered = constructor.getGenericArgs();
            boolean diamond = recovered.isEmpty()
              || (recovered.size() == 1 && recovered.get(0) == GenericType.DUMMY_VAR);
            if (diamond && InvocationExprent.isLambdaBody(this)) {
              List<VarType> implied = impliedArguments(upperBound);
              if (implied != null) {
                impliedConstructorArgs = implied;
              }
            }
            return ret.type != CodeType.VOID ? ret : getExprType();
          }
          else {
            Map<VarType, VarType> genericsMap = new HashMap<>();
            this.gatherGenerics(upperBound, sig.genericType, genericsMap);
            this.getGenericArgs(sig.fparameters, genericsMap, genericArgs);
            VarType _new = sig.genericType.remap(genericsMap);
            if (sig.genericType != _new) {
              return _new;
            }
          }
        }
      }
      else if (newType.arrayDim > 0 && !lstArrayElements.isEmpty() && newType.value.equals(VarType.VARTYPE_OBJECT.value)) {
        VarType first = lstArrayElements.get(0).getInferredExprType(null);
        if (first.type == CodeType.GENVAR) {
          boolean matches = true;
          for (int i = 1; i < lstArrayElements.size(); ++i) {
            VarType type = lstArrayElements.get(i).getInferredExprType(null);
            if (!type.equals(first)) {
              matches = false;
              break;
            }
          }
          if (matches) {
            return first.resizeArrayDim(newType.arrayDim);
          }
        }
      }
    }

    if (lambda) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);

      if (node != null) {

        VarType classType = node.anonymousClassType;
        StructClass cls = DecompilerContext.getStructContext().getClass(classType.value);
        MethodDescriptor desc = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);
        StructClass methodCls = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);

        if (cls != null && cls.getSignature() != null && methodCls != null) {
          StructMethod refMethod = cls.getMethod(getLambdaMethodKey());
          StructMethod method = methodCls.getMethod(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);

          if (method != null && refMethod != null && refMethod.getSignature() != null) {
            GenericType ret = cls.getSignature().genericType;

            HashMap<VarType, VarType> genericsMap = new HashMap<>();
            Map<VarType, List<VarType>> named = getNamedGenerics();

            gatherGenerics(upperBound, ret, genericsMap);

            HashMap<VarType, VarType> instanceMap = new HashMap<>();
            if (isMethodReference() && methodCls.getSignature() != null) {
              VarType first = ret.getArguments().get(0);
              if (constructor.getInstance() != null) {
                VarType instanceType = constructor.getInstance().getInferredExprType(null);
                if (instanceType.isGeneric()) {
                  methodCls.getSignature().genericType.mapGenVarsTo((GenericType)instanceType, instanceMap);
                }
              }
              else if (method.getSignature() != null) {
                for (int i = 0; i < method.getSignature().parameterTypes.size(); ++i) {
                  VarType mtype = method.getSignature().parameterTypes.get(i);
                  VarType rtype = refMethod.getSignature().parameterTypes.get(i);
                  if (mtype.type == CodeType.GENVAR && rtype.type == CodeType.GENVAR) {
                    if (genericsMap.containsKey(rtype)) {
                      instanceMap.put(mtype, genericsMap.get(rtype));
                    }
                  }
                }
                // A no-bound instance reference (`Type::method`) has no receiver expression: the
                // SAM's first parameter is the receiver. Projecting that recorded parameter onto
                // the referenced class solves the class's own variables, so the method's return
                // type is instantiated instead of leaking the class's T into the call's scope.
                // Only a projection onto the referenced class with a complete binding is used.
                if (!node.lambdaInformation.is_content_method_static && first != null && methodCls.getSignature() != null) {
                  VarType receiver = stripReferenceWildcard(first.remap(genericsMap));
                  GenericType methodType = methodCls.getSignature().genericType;
                  if (receiver != null && receiver.type == CodeType.OBJECT && receiver.value != null
                    && methodType != null && methodType.value != null) {
                    VarType view = receiver.value.equals(methodType.value)
                      ? receiver : GenericType.getGenericSuperType(receiver, methodType);
                    if (view instanceof GenericType viewType && viewType.value != null
                      && viewType.value.equals(methodType.value)) {
                      Map<VarType, VarType> binding = new HashMap<>();
                      methodType.mapGenVarsTo(viewType, binding);
                      binding.forEach((from, to) -> {
                        if (to != null && !GenericType.DUMMY_VAR.equals(to)) {
                          instanceMap.put(from, to);
                        }
                      });
                    }
                  }
                }
              }
            }

            // generated lambda methods have no generic info, so only map to generic var parameters
            List<VarType> types = method.getSignature() != null ? method.getSignature().parameterTypes : Arrays.asList(desc.params);
            for (int i = 0; i < types.size(); ++i) {
              List<VarType> parameterTypes = refMethod.getSignature().parameterTypes;
              if (i < parameterTypes.size() && parameterTypes.get(i).type == CodeType.GENVAR) {
                if (!genericsMap.containsKey(parameterTypes.get(i))) {
                  VarType realType = types.get(i);
                  StructClass typeCls = DecompilerContext.getStructContext().getClass(realType.value);
                  if (typeCls != null && typeCls.getSignature() != null && !realType.equals(typeCls.getSignature().genericType)) {
                    realType = typeCls.getSignature().genericType.resizeArrayDim(realType.arrayDim);
                  }
                  genericsMap.put(parameterTypes.get(i), realType);
                }
              }
            }

            if (refMethod.getSignature().returnType.type == CodeType.GENVAR) {
              VarType key = refMethod.getSignature().returnType;
              if (method.getName().equals(CodeConstants.INIT_NAME)) {
                if (methodCls.getSignature() != null) {
                  genericsMap.put(key, methodCls.getSignature().genericType);
                }
                else {
                  genericsMap.put(key, GenericType.parse("L" + methodCls.qualifiedName + ";"));
                }
              }
              else if (method.getSignature() != null || !desc.ret.equals(VarType.VARTYPE_OBJECT)) {
                VarType current = genericsMap.get(key);
                VarType returnType = method.getSignature() != null ? method.getSignature().returnType.remap(instanceMap) : desc.ret;
                StructClass retCls = returnType == null ? null : DecompilerContext.getStructContext().getClass(returnType.value);

                if (!isMethodReference() && retCls != null && retCls.getSignature() != null && !retCls.getSignature().genericType.equalsExact(returnType)) {
                  VarType retUB = current != null && current.equals(returnType) ? current : returnType;
                  VarType realType = getLambdaReturnType(node, refMethod, retUB, genericsMap);
                  if (realType != null) {
                    returnType = realType;
                  }
                }

                boolean add = current == null || returnType == null || returnType.isGeneric() ||
                  (!returnType.equals(genericsMap.get(key)) && (current.type != CodeType.GENVAR || !named.containsKey(current)));
                if (add) {
                  VarType prior = genericsMap.get(key);
                  boolean addToMap = true;
                  if (prior != null) {
                    if (prior.isGeneric() && !((GenericType)prior).isTypeUnfinished() && DecompilerContext.getStructContext().instanceOf(returnType.value, prior.value)) {
                      addToMap = false;
                    }
                  }

                  if (addToMap) {
                    genericsMap.put(key, returnType);
                  }
                }
              }
            }

            ret.getAllGenericVars().forEach(from -> {
              genericsMap.putIfAbsent(from, GenericType.DUMMY_VAR);
            });

            if (!genericsMap.isEmpty()) {
              VarType _new = ret.remap(genericsMap);
              if (_new != ret) {
                if (!_new.isGeneric() || !((GenericType)_new).hasUnknownGenericType(named.keySet())) {
                  inferredLambdaType = _new;
                  wildcardTargetLambda = false;
                }
                else if (inferredLambdaType == null && _new.isGeneric()
                  && _new.value.equals(classType.value) && cls.getSignature() != null) {
                  // The target still names the functional interface the lambda was built for,
                  // even though a wildcard in it leaves a variable unresolved. The interface's
                  // recorded SAM return type is then the target of the body's returns.
                  inferredLambdaType = _new;
                  wildcardTargetLambda = true;
                }
                return _new;
              }
            }
          }
        }
        else {
          inferredLambdaType = classType;
          wildcardTargetLambda = false;
        }
        // The expected type of a functional argument is often the wildcard form the called
        // method declares (Function<? super T, ? extends R>); the mapping above cannot bind
        // the interface's variables through the wildcards, but that recorded type still says
        // which interface and which arguments the lambda was built for. Keep it so the body's
        // target type comes from the class file's signature rather than from nowhere.
        if (inferredLambdaType == null && upperBound != null && upperBound.isGeneric()
          && upperBound.value.equals(classType.value) && cls != null && cls.getSignature() != null) {
          inferredLambdaType = upperBound;
          wildcardTargetLambda = true;
        }
      }
    }

    return getExprType();
  }

  @Override
  public CheckTypesResult checkExprTypeBounds() {
    CheckTypesResult result = new CheckTypesResult();

    if (newType.arrayDim != 0) {
      for (Exprent dim : lstDims) {
        result.addExprLowerBound(dim, VarType.VARTYPE_BYTECHAR);
        result.addExprUpperBound(dim, VarType.VARTYPE_INT);
      }

      if (newType.arrayDim == 1) {
        VarType leftType = newType.decreaseArrayDim();
        for (Exprent element : lstArrayElements) {
          result.addExprLowerBound(element, VarType.findFamilyBottom(leftType.typeFamily));
          result.addExprUpperBound(element, leftType);
        }
      }
    }
    else if (constructor != null) {
      return constructor.checkExprTypeBounds();
    }

    return result;
  }

  @Override
  public List<Exprent> getAllExprents(List<Exprent> lst) {
    if (newType.arrayDim != 0) {
      lst.addAll(lstDims);
      lst.addAll(lstArrayElements);
    }
    else if (constructor != null) {
      Exprent constructor = this.constructor.getInstance();
      if (constructor != null) { // should be true only for a lambda expression with a virtual content method
        lst.add(constructor);
      }
      lst.addAll(this.constructor.getLstParameters());
    }

    return lst;
  }

  @Override
  public Exprent copy() {
    List<Exprent> lst = new ArrayList<>();
    for (Exprent expr : lstDims) {
      lst.add(expr.copy());
    }

    NewExprent ret = new NewExprent(newType, lst, bytecode);
    ret.setConstructor(constructor == null ? null : (InvocationExprent)constructor.copy());
    ret.setLstArrayElements(DecHelper.copyExprentList(lstArrayElements));
    ret.setDirectArrayInit(directArrayInit);
    ret.setAnonymous(anonymous);
    ret.setEnumConst(enumConst);
    return ret;
  }

  @Override
  public int getPrecedence() {
    return 1; // precedence of new
  }

  /** An expression kind whose line table entry is its own, not inherited from the statement. */
  private static boolean hasOwnLine(Exprent element) {
    return element instanceof InvocationExprent || element instanceof NewExprent
      || element instanceof FunctionExprent;
  }

  /**
   * The enclosing call's line when this creation's `new` has no line-table entry of its own.
   * The allocation then inherits the preceding instruction's line, which says nothing about
   * where the creation's text sits; written as an argument, it sits on the enclosing call's
   * line, which is the only line the first argument may be compared with. An enclosing
   * constructor is not that line: its invoke is emitted after its own arguments, so the entry
   * it inherits names where the argument list ended, not where the enclosing call's text sits.
   */
  private int enclosingCreationLine() {
    int newOffset = bytecode == null || bytecode.isEmpty() ? -1 : bytecode.nextSetBit(0);
    if (newOffset > 0 && !RoundTrip.lineStartsAt(newOffset) && InvocationExprent.inArgument()
        && !InvocationExprent.enclosingCallIsInit()) {
      return InvocationExprent.enclosingCallLine();
    }
    return -1;
  }

  /**
   * The line the anonymous class's own constructor is recorded on, or -1. javac emits that code
   * after the creation's arguments, so the line is where the source closed the argument list —
   * the `new` line for a creation written on one line, later when the arguments span lines.
   */
  public int anonymousConstructorLine() {
    MethodWrapper wrapper = anonymousConstructor();
    return wrapper == null ? -1 : RoundTrip.methodLine(wrapper.methodStruct);
  }

  /**
   * Whether the creation prints its head as one token run ending in an empty argument list:
   * {@code new T()} whose recorded constructor parameters are all synthetic captures the printer
   * masks. Only then does the line javac records for the anonymous class's implicit constructor —
   * where the source closed that empty list — also name the line the {@code new} token sits on.
   */
  public boolean printsHeadWithoutArguments() {
    if (constructor == null || isEnumConst()) {
      return false;
    }
    List<Exprent> parameters = constructor.getLstParameters();
    if (parameters.isEmpty()) {
      return true;
    }
    if (!anonymous || lambda) {
      return false;
    }
    List<VarVersionPair> mask = ExprUtil.getSyntheticParametersMask(newType.value,
      constructor.getStringDescriptor(), parameters.size());
    if (mask == null) {
      return false;
    }
    for (int i = 0; i < parameters.size(); i++) {
      if (i >= mask.size() || mask.get(i) == null) {
        return false;
      }
    }
    return true;
  }

  /**
   * The implicit constructor of the anonymous class this creation allocates, or null. A lambda is
   * an anonymous class too, but its code lives in the enclosing class file, and that file's
   * constructors say nothing about the lambda's line.
   */
  private MethodWrapper anonymousConstructor() {
    if (!anonymous || lambda || newType == null) {
      return null;
    }
    ClassNode child = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (child == null || child.getWrapper() == null) {
      return null;
    }
    for (MethodWrapper wrapper : child.getWrapper().getMethods()) {
      if (CodeConstants.INIT_NAME.equals(wrapper.methodStruct.getName())) {
        return wrapper;
      }
    }
    return null;
  }

  /** An element whose first token is on its own line: not a chained call's later qualifier. */
  private static boolean startsOnItsLine(Exprent element) {
    if (element instanceof InvocationExprent invocation && invocation.getInstance() != null) {
      int receiver = RoundTrip.sourceLine(invocation.getInstance());
      int call = RoundTrip.sourceLine(invocation);
      return receiver < 0 || call < 0 || receiver == call;
    }
    return true;
  }

  /**
   * The line an array element starts on. An anonymous creation's allocation only inherits the
   * enclosing initializer's line, while the class's own constructor is recorded where the source
   * closed the creation's argument list — the element's line when its head was written on one
   * line. A variable or constant carries no entry and keeps returning -1 through the table.
   */
  private static int elementLine(Exprent element) {
    if (element instanceof NewExprent creation && creation.isAnonymous() && !creation.isLambda()) {
      int line = creation.anonymousConstructorLine();
      if (line >= 0) {
        return line;
      }
    }
    return RoundTrip.sourceLine(element);
  }

  /**
   * A type annotation recorded on this array-creation expression ({@code target_type 0x44}) whose
   * path descends one array level names the element type: the source wrote it between
   * {@code new} and the element type, as in {@code new @Nullable String[128]}.
   */
  private void appendNewExpressionTypeAnnotations(TextBuffer buf) {
    if (!RoundTrip.selector("typeuse") || bytecode == null || bytecode.isEmpty()) {
      return;
    }
    // A field's initializer is printed outside a method-writing context; the writer names the
    // owning method through CURRENT_STRUCT_METHOD there, and CURRENT_METHOD_WRAPPER elsewhere.
    StructMethod method = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_STRUCT_METHOD);
    if (method == null) {
      MethodWrapper wrapper = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_METHOD_WRAPPER);
      method = wrapper == null ? null : wrapper.methodStruct;
    }
    if (method == null) {
      return;
    }
    for (Key<?> key : ClassWriter.TYPE_ANNOTATION_ATTRIBUTES) {
      StructTypeAnnotationAttribute attribute =
        method.getAttribute((Key<StructTypeAnnotationAttribute>) key);
      if (attribute == null) {
        continue;
      }
      for (TypeAnnotation annotation : attribute.getAnnotations()) {
        if (annotation.getTargetType() != TypeAnnotation.EXPR_NEW) {
          continue;
        }
        // javac anchors the expression target on the dimension expression's first instruction
        // (the `128` of `new String[128]`), not on the array-creating instruction itself.
        boolean anchor = bytecode.get(annotation.getIndex());
        for (int i = 0; !anchor && i < lstDims.size(); i++) {
          BitSet dimRange = new BitSet();
          lstDims.get(i).getBytecodeRange(dimRange);
          anchor = dimRange.get(annotation.getIndex());
        }
        if (!anchor) {
          continue;
        }
        TypeAnnotation.PathValue[] path = annotation.path;
        // Only the element position of this array is printable here; any other path would need a
        // different textual slot and is left to the printer's comment dump.
        if (path.length != 1 || path[0].kind() != TypeAnnotation.PathKind.DEEPER_ARRAY) {
          continue;
        }
        AnnotationExprent annotationExprent = annotation.getAnnotation();
        if (annotationExprent.didWriteAlready()) {
          continue;
        }
        annotationExprent.setDidWriteAlready(true);
        buf.append(annotationExprent.toJava(-1)).append(' ');
      }
    }
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    if (anonymous) {
      ClassNode child = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);

      boolean selfReference = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE) == child;

      // IDEA-204310 - avoid backtracking later on for lambdas (causes spurious imports)
      int headLines = -1;
      if (!enumConst && (!lambda || DecompilerContext.getOption(IFernflowerPreferences.LAMBDA_TO_ANONYMOUS_CLASS))) {
        headLines = buf.countLines();
        TextBuffer enclosing = null;

        if (!lambda && constructor != null) {
          enclosing = getQualifiedNewInstance(child.anonymousClassType.value, constructor.getLstParameters(), indent);
          if (enclosing != null) {
            buf.append(enclosing).append('.');
          }
        }

        buf.append("new ");

        if (selfReference) {
          buf.append("<anonymous constructor>");
        } else {
          String typename = ExprProcessor.getCastTypeName(child.anonymousClassType);
          if (enclosing != null) {
            ClassNode anonymousNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(child.anonymousClassType.value);
            if (anonymousNode != null) {
              typename = anonymousNode.simpleName;
            }
            else {
              typename = typename.substring(typename.lastIndexOf('.') + 1);
            }
          }

          boolean appendType = true;
          if (child.getWrapper() != null) {
            GenericClassDescriptor descriptor = child.getWrapper().getClassStruct().getSignature();
            if (descriptor != null) {
              if (descriptor.superinterfaces.isEmpty()) {
                appendAnonymousSuperType(buf, descriptor.superclass, child);
              } else {
                if (descriptor.superinterfaces.size() > 1 && !lambda) {
                  DecompilerContext.getLogger().writeMessage("Inconsistent anonymous class signature: " + child.classStruct.qualifiedName,
                    IFernflowerLogger.Severity.WARN);
                }
                appendAnonymousSuperType(buf, descriptor.superinterfaces.get(0), child);
              }
              appendType = false;
            }
          }

          if (appendType) {
            buf.appendCastTypeName(typename, child.anonymousClassType);
          }
        }
      }

      if (!lambda && constructor != null) {
        List<VarType> args = constructor.getGenericArgs();
        boolean diamond = args.size() == 1 && args.get(0) == GenericType.DUMMY_VAR;
        if (args.isEmpty() && RoundTrip.selector("rt-diamond")
            && hasTypeParameters(newType)) {
          // No type arguments were recovered, but javac can infer them from the context; the
          // original wrote `new Foo<>()`, and the raw type would break the caller's inference.
          buf.append("<>");
          args = List.of(GenericType.DUMMY_VAR);
          diamond = false;
        } else {
          appendParameters(buf, args);
        }
        buf.append('(');
        if (diamond) {
          InvocationExprent.enterPoly();
        }
        boolean anonymousCreation = child != null;
        if (anonymousCreation) {
          InvocationExprent.enterAnonymousCreation();
        }
        try {
          constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
          constructor.setCallerEnclosingLine(enclosingCreationLine());
          constructor.setCallerTextLine(InvocationExprent.creationTextLine(this));
          buf.append(constructor.appendParamList(indent));
        } finally {
          if (anonymousCreation) {
            InvocationExprent.exitAnonymousCreation();
          }
          if (diamond) {
            InvocationExprent.exitPoly();
          }
        }
      }
      else {
        appendParameters(buf, genericArgs);
        buf.append('(');
      }

      buf.append(')');

      // The anonymous class's implicit constructor prints no text of its own: javac records its
      // first instruction on the line the source closed the creation's argument list on, so that
      // entry anchors to the closing parenthesis. Without it the line aligner cannot place a
      // creation moved to its own line, and the movement would shift every line below instead.
      // The creation has to print its head on one line to own the anchor: a receiver in a chain
      // continues on later lines, and those entries say where its text ends, not this one.
      if (!selfReference && !lambda && child != null && !isQualifier && headLines >= 0
          && buf.countLines() == headLines) {
        MethodWrapper anonymousInit = anonymousConstructor();
        if (anonymousInit != null) {
          buf.addBytecodeMappingAt(buf.length(), 0, child.classStruct.qualifiedName,
            InterpreterUtil.makeUniqueKey(anonymousInit.methodStruct.getName(),
              anonymousInit.methodStruct.getDescriptor()));
        }
      }

      if (enumConst && buf.length() == 2) {
        buf.setLength(0);
      }

      if (lambda) {
        if (!DecompilerContext.getOption(IFernflowerPreferences.LAMBDA_TO_ANONYMOUS_CLASS)) {
          buf.setLength(0);  // remove the usual 'new <class>()', it will be replaced with lambda style '() ->'
        }
        setLambdaGenericTypes();
        Exprent methodObject = constructor == null ? null : constructor.getInstance();
        if (methodObject == null && constructor != null && child != null
            && child.lambdaInformation.is_content_method_static && !constructor.getLstParameters().isEmpty()) {
          // A static lambda bridge takes the captured receiver as its first parameter; a method
          // reference bound to it prints that value as the reference's qualifier.
          methodObject = constructor.getLstParameters().get(0);
        }
        if (methodObject != null && isMethodReference()) {
          forceRecordedReceiverType(methodObject);
        }
        // The lambda's text starts where the argument printer placed this argument: the call's
        // own line when it follows the opening parenthesis on it, or the line the previous
        // argument ended on when it continues that line. The invokedynamic's own table entry is
        // only inherited and can name an earlier line when the enclosing call spans lines, so it
        // is the fallback. A body line later than this one is a break the source had.
        int callLine = Math.max(InvocationExprent.argumentTextStartLine(),
          InvocationExprent.enclosingCallLine());
        // The target records the lambda's creation on the call's line when the source wrote them
        // together, and the lambda's own text never maps it; the table-entry gate keeps a lambda
        // whose creation the target puts on another line from being pulled to the call's. The
        // anchor is for the line aligner only: as a pool-order position it would move the
        // constant-name pass's nearest-item point inside the body.
        // A lambda whose head stands outside any call -- the expression of a switch arm, a
        // field initializer, a return value -- has enclosingCallLine() == -1, so the gate above
        // can never hold and the head's line is only inherited from the dispatching statement.
        // The invokedynamic still records the head token's own line; when the target's table
        // starts a line exactly at it, the text start may anchor to it. An entry that does not
        // start a line says nothing about where the head sits, so it is not used.
        boolean headOnItsLine = RoundTrip.sourceLine(this) == InvocationExprent.enclosingCallLine();
        if (!headOnItsLine && InvocationExprent.enclosingCallLine() < 0
            && bytecode != null && !bytecode.isEmpty()) {
          int creation = bytecode.nextSetBit(0);
          headOnItsLine = RoundTrip.hasLineEntryAt(creation) && RoundTrip.lineStartsAt(creation);
        }
        if (!isMethodReference() && !InvocationExprent.enclosingCallIsInit()
            && bytecode != null && !bytecode.isEmpty() && headOnItsLine) {
          buf.addAlignOnlyBytecodeMapping(bytecode);
        }
        new ClassWriter().classLambdaToJava(child, buf, methodObject, indent,
          callLine >= 0 ? callLine : RoundTrip.sourceLine(this), methodReferenceQualifier(), getFunctionalReturnType(),
          getFunctionalParameterTypes());
        if (isMethodReference() && RoundTrip.selector("arg-head-line")) {
          // A method reference has no body method whose table could anchor its text: javac records
          // the invokedynamic (and the null check of a captured receiver) on the line the
          // reference is written on, and only that entry can tell the aligner where the text sits.
          buf.addBytecodeMapping(bytecode);
        }
      }
      else if (!selfReference) {
        String regionClass = child == null || child.classStruct == null ? null : child.classStruct.qualifiedName;
        int region = regionClass == null ? -1 : buf.beginRegion(regionClass);
        try {
          new ClassWriter().writeClass(child, buf, indent);
        }
        finally {
          if (region >= 0) {
            buf.endRegion(regionClass, region);
          }
        }
      }
    }
    else if (directArrayInit) {
      VarType leftType = newType.decreaseArrayDim();
      buf.append('{');
      if (!lstArrayElements.isEmpty()) {
        buf.pushNewlineGroup(indent, 2);
        buf.appendPossibleNewline();
        buf.pushNewlineGroup(indent, 0);
      }
      for (int i = 0; i < lstArrayElements.size(); i++) {
        if (i > 0) {
          buf.append(",").appendPossibleNewline(" ");
        }
        ExprProcessor.getCastedExprent(lstArrayElements.get(i), leftType, buf, indent, false);
      }
      if (!lstArrayElements.isEmpty()) {
        buf.popNewlineGroup();
        buf.appendPossibleNewline("", true);
        buf.popNewlineGroup();
      }
      buf.append('}');
    }
    else if (newType.arrayDim == 0) {
      if (!enumConst) {
        TextBuffer enclosing = null;
        boolean implicitEnclosing = constructor != null
          && implicitEnclosingInstance(newType.value, constructor.getLstParameters());

        if (constructor != null) {
          // Evaluate the qualified form as before even when the source wrote the implicit one:
          // its printing seeds types the surrounding expressions rely on.
          enclosing = getQualifiedNewInstance(newType.value, constructor.getLstParameters(), indent);
          if (enclosing != null && !implicitEnclosing) {
            buf.append(enclosing).append('.');
          }
        }

        buf.append("new ");
        // The allocation's own instruction sits where `new` is printed. Without this mapping the
        // line aligner cannot see the line the allocation is on: the enclosing statement's store
        // is mapped at the statement's start, so an allocation on a later line would be pulled
        // back to the declaration's.
        buf.addBytecodeMapping(bytecode);

        String typename = ExprProcessor.getTypeName(newType);
        if (enclosing == null) {
          String qualified = qualifiedInnerNewType(newType);
          if (qualified != null && !implicitEnclosing) {
            typename = qualified;
          }
          else if (expectedCreationType instanceof GenericType expected && expected.getParent() != null
              && newType.value != null && newType.value.equals(expected.value)) {
            // A member class of a generic outer class names the outer's type argument; the
            // allocation's own instruction only carries the erased class, and the recorded
            // target is where the source's `Outer<T>.Inner` spelling survives.
            typename = ExprProcessor.getTypeName(expected);
          }
        }
        else if (!implicitEnclosing) {
          ClassNode newNode = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
          if (newNode != null) {
            typename = newNode.simpleName;
          }
          else {
            typename = typename.substring(typename.lastIndexOf('.') + 1);
          }
        }
        buf.appendTypeName(typename, newType);
      }

      if (constructor != null) {
        int start = enumConst ? 2 : 0;
        if (!enumConst || start < constructor.getLstParameters().size()) {
          List<VarType> args = forcedConstructorArgs != null ? forcedConstructorArgs
            : impliedConstructorArgs != null ? impliedConstructorArgs : constructor.getPrintedGenericArgs();
          if (targetedDiamond && forcedConstructorArgs == null) {
            // The recovered arguments are only subtypes of the expected ones; printing them
            // would pin javac to a type the target rejects, so the source wrote the diamond.
            buf.append("<>");
            constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
            constructor.setCallerEnclosingLine(enclosingCreationLine());
            constructor.setCallerTextLine(InvocationExprent.creationTextLine(this));
            buf.append('(').append(constructor.appendParamList(indent)).append(')');
            return buf;
          }
          // A receiver has no target type. A diamond printed because the value sits inside an
          // enclosing argument list would infer its arguments from the constructor's arguments
          // alone, and when those leave a variable unconstrained javac closes it on its bound:
          // the chained receiver then loses the parameterization the caller needs. The original
          // wrote the raw type in that position, and erasure makes the two spellings identical.
          boolean receiverDiamond = args.isEmpty() && isQualifier;
          if (args.isEmpty() && receiverDiamond && printableCreationArguments(expectedCreationArgs)) {
            // The chain's target fixes the receiver's arguments completely, and the source
            // pinned them: a diamond there has no target to infer from.
            appendParameters(buf, expectedCreationArgs);
          }
          else if (args.isEmpty() && RoundTrip.selector("rt-diamond") && hasTypeParameters(newType)
              && !receiverDiamond && (InvocationExprent.inArgument() || expectedCreationType != null)) {
            // No recovered type arguments, but javac infers them from the context; the original
            // wrote the diamond, and a raw type would break the caller's inference.
            buf.append("<>");
          } else {
            appendParameters(buf, args);
          }
          constructor.setCallerOpeningLine(RoundTrip.sourceLine(this));
          constructor.setCallerEnclosingLine(enclosingCreationLine());
          constructor.setCallerTextLine(InvocationExprent.creationTextLine(this));
          buf.append('(').append(constructor.appendParamList(indent)).append(')');
        }
      }
    }
    else if (isVarArgParam) {
      // just print the array elements
      VarType leftType = newType.decreaseArrayDim();
      // The array's own line is the packaging instruction's, which inherits whichever call the
      // elements are arguments of; the elements' lines are only comparable with that call's.
      int callLine = InvocationExprent.enclosingCallLine();
      int previousEnd = callLine >= 0 ? callLine : RoundTrip.sourceLine(this);
      // An invocation, a creation and a conditional expression carry a line entry of their own; a
      // variable or constant carries none, so its line is whatever the statement before it left
      // and cannot move the baseline. The last element that does carry one stays the comparison
      // point across any run of variables and fields: an element after them still proves its own
      // break when its entry sits below that line, and the field simply shares the earlier line
      // in the printed text, which the table gives no entry of its own to contradict.
      boolean enabled = RoundTrip.selector("vararg-elements");
      for (int i = 0; i < lstArrayElements.size(); i++) {
        Exprent element = lstArrayElements.get(i);
        int line = RoundTrip.sourceLine(element);
        int end = RoundTrip.sourceLineEnd(element);
        // An element the original put on a later line starts a line here. A later element whose
        // own line is inherited but whose invoke is later was written on that later line, for the
        // same reason as an argument.
        boolean later = enabled && line >= 0 && previousEnd >= 0 && line > previousEnd;
        boolean ownLater = enabled && element instanceof InvocationExprent
          && line >= 0 && previousEnd >= 0 && line <= previousEnd && end > previousEnd;
        boolean elementStartsLine = later || ownLater;
        if (i > 0) {
          buf.append(",");
          if (elementStartsLine) {
            buf.appendLineSeparator();
          } else {
            buf.appendPossibleNewline(" ");
          }
        } else if (elementStartsLine) {
          buf.appendLineSeparator();
        }

        // new String[][]{{"abc"}, {"DEF"}} => new String[]{"abc"}, new String[]{"DEF"}
        if (element instanceof NewExprent) {
          ((NewExprent) element).setDirectArrayInit(false);
        }
        int savedTextStart = elementStartsLine ? InvocationExprent.enterVarargElement(element) : -1;
        try {
          ExprProcessor.getCastedExprent(element, leftType, buf, indent, false);
        } finally {
          if (elementStartsLine) {
            InvocationExprent.exitVarargElement(savedTextStart);
          }
        }
        if (end >= 0 && (element instanceof InvocationExprent || element instanceof NewExprent
            || element instanceof FunctionExprent)) {
          previousEnd = end;
        }
      }

      // if there is just one element of Object[] type it needs to be casted to resolve ambiguity
      if (lstArrayElements.size() == 1) {
        VarType elementType = lstArrayElements.get(0).getExprType();
        if (elementType.type == CodeType.OBJECT && elementType.value.equals("java/lang/Object") && elementType.arrayDim >= 1) {
          buf.prepend("(Object)");
        }
      }
    }
    else {
      buf.append("new ");
      // The creation's own instruction sits where `new` is printed, exactly as for an object
      // allocation; without this mapping the aligner cannot see the line the array creation is
      // on and the size's iconst is left to the statement's other anchors.
      buf.addBytecodeMapping(bytecode);
      appendNewExpressionTypeAnnotations(buf);
      VarType component = printedArrayComponent();
      buf.appendTypeName(component != null ? component : newType);

      if (lstArrayElements.isEmpty()) {
        for (int i = 0; i < newType.arrayDim; i++) {
          buf.append('[');
          if (i < lstDims.size()) {
            if (lstDims.get(i).type == Type.CONST) {
              ((ConstExprent)lstDims.get(i)).adjustConstType(VarType.VARTYPE_INT);
            }
            buf.append(lstDims.get(i).toJava(indent));
          }
          buf.append(']');
        }
      }
      else {
        for (int i = 0; i < newType.arrayDim; i++) {
          buf.append("[]");
        }

        VarType leftType = newType.decreaseArrayDim();
        buf.append('{');
        buf.pushNewlineGroup(indent, 1);
        // The target's table gives every element its own line when the source wrote the array
        // across lines; an equal or absent line is no evidence of a break.
        int arrayLine = RoundTrip.sourceLine(this);
        Exprent firstElement = lstArrayElements.get(0);
        int firstLine = elementLine(firstElement);
        // A variable or constant carries no line entry: its line is inherited from the statement,
        // so a gap from it to a later element proves nothing. Only an expression with its own
        // entry can anchor a break, on either side.
        boolean firstOwnLine = hasOwnLine(firstElement) && startsOnItsLine(firstElement);
        if (arrayLine >= 0 && firstOwnLine && firstLine > arrayLine) {
          buf.appendLineSeparator().appendIndent(indent + 1);
        } else {
          buf.appendPossibleNewline();
        }
        buf.pushNewlineGroup(indent, 0);
        boolean previousOwnLine = firstOwnLine;
        for (int i = 0; i < lstArrayElements.size(); i++) {
          if (i > 0) {
            Exprent element = lstArrayElements.get(i);
            buf.append(",");
            int previousLine = elementLine(lstArrayElements.get(i - 1));
            int line = elementLine(element);
            if (previousOwnLine && hasOwnLine(element) && startsOnItsLine(element)
              && previousLine >= 0 && line > previousLine) {
              buf.appendLineSeparator().appendIndent(indent + 1);
            } else {
              buf.appendPossibleNewline(" ");
            }
          }
          ExprProcessor.getCastedExprent(lstArrayElements.get(i), leftType, buf, indent, false);
          previousOwnLine = hasOwnLine(lstArrayElements.get(i));
        }
        buf.popNewlineGroup();
        buf.appendPossibleNewline("", true);
        buf.append('}');
        buf.popNewlineGroup();
      }
    }

    return buf;
  }

  // TODO move to InvocationExprent
  public static boolean probablySyntheticParameter(String className) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(className);
    return node != null && node.type == ClassNode.Type.ANONYMOUS;
  }

  public static TextBuffer getQualifiedNewInstance(String classname, List<Exprent> lstParams, int indent) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);

    if (node != null && node.type != ClassNode.Type.ROOT && node.type != ClassNode.Type.LOCAL
        && (node.access & CodeConstants.ACC_STATIC) == 0) {
      if (!lstParams.isEmpty()) {
        Exprent enclosing = lstParams.get(0);

        boolean isQualifiedNew = false;

        if (enclosing instanceof VarExprent) {
          VarExprent varEnclosing = (VarExprent)enclosing;

          StructClass current_class = ((ClassNode)DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE)).classStruct;
          String this_classname = varEnclosing.getProcessor().getThisVars().get(new VarVersionPair(varEnclosing));

          if (!current_class.qualifiedName.equals(this_classname)) {
            isQualifiedNew = true;
          }
        }
        else {
          isQualifiedNew = true;
        }

        if (isQualifiedNew) {
          return enclosing.toJava(indent);
        }
      }
    }

    return null;
  }

  /**
   * True when the creation's enclosing instance is a lexically enclosing {@code this} and the
   * target did not null-check it. javac emits {@code dup; Objects.requireNonNull; pop} after the
   * enclosing expression of a qualified creation inside a nested class, and nothing for the
   * implicit form, so the absence of that check is the source's unqualified {@code new Inner()}.
   */
  private boolean implicitEnclosingInstance(String classname, List<Exprent> lstParams) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(classname);
    if (node == null || node.type == ClassNode.Type.ROOT || node.type == ClassNode.Type.LOCAL
        || (node.access & CodeConstants.ACC_STATIC) != 0 || lstParams.isEmpty()
        || !(lstParams.get(0) instanceof VarExprent enclosing)) {
      return false;
    }
    ClassNode current = (ClassNode) DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_NODE);
    if (current == null) {
      return false;
    }
    String owner = enclosing.getProcessor().getThisVars().get(new VarVersionPair(enclosing));
    if (owner == null || current.classStruct.qualifiedName.equals(owner)) {
      // Not a captured outer instance; the printer already leaves the current class's own this
      // unqualified.
      return false;
    }
    return !enclosingInstanceChecked(this);
  }

  /** True when the target emitted the null check javac gives a qualified member-class creation. */
  private static boolean enclosingInstanceChecked(Exprent creation) {
    StructMethod method = RoundTrip.currentMethod();
    if (method == null || creation.bytecode == null || creation.bytecode.isEmpty()) {
      return true;
    }
    StructClass cl = DecompilerContext.getStructContext().getClass(method.getClassQualifiedName());
    if (cl == null) {
      return true;
    }
    boolean hadData = method.getInstructionSequence() != null;
    try {
      method.expandData(cl);
      FullInstructionSequence seq = method.getInstructionSequence();
      if (seq == null) {
        return true;
      }
      Integer index = seq.offsetToIndex().get(creation.bytecode.nextSetBit(0));
      if (index == null) {
        return true;
      }
      for (int i = index; i < Math.min(seq.length(), index + 32); i++) {
        Instruction ins = seq.getInstr(i);
        if (ins.opcode == CodeConstants.opc_invokespecial) {
          return false;
        }
        if (ins.opcode == CodeConstants.opc_invokestatic) {
          LinkConstant target = cl.getPool().getLinkConstant(ins.operand(0));
          if (target != null && "java/util/Objects".equals(target.classname)
              && "requireNonNull".equals(target.elementname)) {
            return true;
          }
        }
      }
      return true;
    } catch (IOException e) {
      return true;
    } finally {
      // The method's data was released before printing; leave it that way.
      if (!hadData) {
        method.releaseResources();
      }
    }
  }

  private static VarType getLambdaReturnType(ClassNode node, StructMethod desc, VarType upperBound, Map<VarType, VarType> genericsMap) {
    ClassWrapper wrapper = node.getWrapper();
    Map<String, VarType> inferredLambdaTypes = Exprent.inferredLambdaTypes.get();

    if (wrapper != null) {
      MethodWrapper mt = wrapper.getMethodWrapper(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);

      if (mt != null && mt.root != null) {
        List<String> paramNames = new ArrayList<>();

        MethodDescriptor md_content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
        MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);

        int index = node.lambdaInformation.is_content_method_static ? 0 : 1;
        int start_index = md_content.params.length - md_lambda.params.length;

        int j = 0;
        for (int i = 0; i < md_content.params.length; i++) {
          if (i >= start_index) {
            VarVersionPair vpp = new VarVersionPair(index, 0);
            VarType curType = mt.varproc.getVarType(vpp);
            VarType infType = desc.getSignature().parameterTypes.get(j++).remap(genericsMap);

            if (infType != null && !infType.equals(VarType.VARTYPE_VOID)) {
              if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
                String varName = mt.varproc.getVarName(vpp);
                paramNames.add(varName);
                inferredLambdaTypes.put(varName, infType);
              }
            }
          }
          index += md_content.params[i].stackSize;
        }

        DummyExitStatement dummyExit = mt.root.getDummyExit();

        for (StatEdge edge : dummyExit.getAllPredecessorEdges()) {
          Statement source = edge.getSource();
          List<Exprent> lstExpr = source.getExprents();

          if (lstExpr != null && !lstExpr.isEmpty()) {
            Exprent expr = lstExpr.get(lstExpr.size() - 1);
            if (expr instanceof ExitExprent) {
              ExitExprent ex = (ExitExprent)expr;
              if (ex.getExitType() == ExitExprent.Type.RETURN) {
                VarType realRetType = ex.getValue().getInferredExprType(upperBound);
                if (realRetType.isGeneric()) {
                  paramNames.forEach(inferredLambdaTypes::remove);
                  return realRetType;
                }
              }
            }
          }
        }

        paramNames.forEach(inferredLambdaTypes::remove);
      }
    }
    return null;
  }

  /** The parameter slot of an enclosed lambda's method that carries this name, or -1. */
  private static int namedParameterSlot(ClassNode child, MethodWrapper enclosed, String name) {
    MethodDescriptor descriptor = MethodDescriptor.parseDescriptor(child.lambdaInformation.content_method_descriptor);
    int slot = child.lambdaInformation.is_content_method_static ? 0 : 1;
    for (VarType parameter : descriptor.params) {
      if (name.equals(enclosed.varproc.getVarName(new VarVersionPair(slot, 0)))) {
        return slot;
      }
      slot += parameter.stackSize;
    }
    return -1;
  }

  private void setLambdaGenericTypes() {
    if (inferredLambdaType != null) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
      StructClass cls = DecompilerContext.getStructContext().getClass(inferredLambdaType.value);

      if (node != null && cls != null) {
        StructMethod desc = cls.getMethod(getLambdaMethodKey());
        ClassWrapper wrapper = node.getWrapper();
        MethodWrapper methodWrapper = wrapper != null ? wrapper.getMethodWrapper(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor) : null;

        if (desc != null && desc.getSignature() != null && methodWrapper != null && methodWrapper.root != null) {
          if (!desc.getClassQualifiedName().equals(inferredLambdaType.value)) {
            StructClass candidate = DecompilerContext.getStructContext().getClass(desc.getClassQualifiedName());
            if (candidate.getSignature() != null) {
              cls = candidate;
              inferredLambdaType = GenericType.getGenericSuperType(inferredLambdaType, candidate.getSignature().genericType);
            }
          }
          if (cls.getSignature() == null) {
            // Without the interface's declared type parameters nothing can be mapped.
            return;
          }

          Map<VarType, VarType> tempMap = new HashMap<>();
          if (inferredLambdaType.isGeneric()) {
            cls.getSignature().genericType.mapGenVarsTo((GenericType)inferredLambdaType, tempMap);
          }

          if (wildcardTargetLambda) {
            // The lambda's interface type came from the wildcard form of the called method's
            // parameter type. Only a recorded return type that resolves to one type variable
            // in the caller's scope is used: a value the body returns as a class can never be
            // that variable, so the source cast it (the cast erases to the same bytes), and
            // the class file's functional interface signature names the variable.
            VarType rawRet = desc.getSignature().returnType;
            VarType mappedRet = rawRet.type == CodeType.GENVAR ? tempMap.get(rawRet.resizeArrayDim(0)) : null;
            // Only the wildcard form (? extends R) is the called method's recorded demand on
            // the body; a return type that is the variable itself carries no such wrapper, and
            // a body's own inference is what the source relied on there.
            if (!(mappedRet instanceof GenericType wildcardRet)
              || wildcardRet.getWildcard() == GenericType.WILDCARD_NO) {
              return;
            }
            VarType retTarget = stripWildcard(mappedRet);
            if (retTarget != null && retTarget.type == CodeType.GENVAR
              && isInScopeTypeVariable(retTarget, getNamedGenerics())) {
              GenericMethodDescriptor genDesc = new GenericMethodDescriptor(Collections.emptyList(), Collections.emptyList(), Collections.emptyList(), retTarget, Collections.emptyList());
              applyReturnTarget(methodWrapper.root, genDesc);
            }
            return;
          }

          MethodDescriptor md_content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
          MethodDescriptor md_lambda = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);

          int index = node.lambdaInformation.is_content_method_static ? 0 : 1;
          int start_index = md_content.params.length - md_lambda.params.length;

          int j = 0;
          for (int i = 0; i < md_content.params.length; i++) {
            if (i >= start_index) {
              VarVersionPair vpp = new VarVersionPair(index, 0);
              VarType curType = methodWrapper.varproc.getVarType(vpp);
              VarType infType = desc.getSignature().parameterTypes.get(j++).remap(tempMap);

              if (infType != null && !infType.equals(VarType.VARTYPE_VOID) && curType != null) {
                if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
                  methodWrapper.varproc.setVarType(vpp, infType);
                  String paramName = methodWrapper.varproc.getVarName(vpp);

                  LinkedList<ClassNode> nested = new LinkedList<>(node.nested);
                  while (!nested.isEmpty()) {
                    ClassNode childNode = nested.removeFirst();
                    nested.addAll(childNode.nested);

                    if (childNode.type == ClassNode.Type.LAMBDA && !childNode.lambdaInformation.is_method_reference) {
                      MethodWrapper enclosedMethod = wrapper.getMethodWrapper(childNode.lambdaInformation.content_method_name, childNode.lambdaInformation.content_method_descriptor);

                      if (enclosedMethod != null) {
                        // A captured variable becomes a leading parameter of the enclosed synthetic
                        // method at a slot of its own; its name, not the outer index, finds it. Only
                        // an erased type is refined: a parameter that already carries generics got
                        // them from its own call site, and overriding those changes the printed
                        // casts of an unrelated chain.
                        int slot = namedParameterSlot(childNode, enclosedMethod, paramName);
                        if (slot >= 0) {
                          VarVersionPair enclosedPair = new VarVersionPair(slot, 0);
                          VarType enclosedType = enclosedMethod.varproc.getVarType(enclosedPair);
                          if (enclosedType == null
                              || (enclosedType.type == CodeType.OBJECT && !enclosedType.isGeneric())) {
                            enclosedMethod.varproc.setVarType(enclosedPair, infType);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            index += md_content.params[i].stackSize;
          }

          VarType curType = md_content.ret;
          VarType infType = desc.getSignature().returnType.remap(tempMap);

          // A method reference's content method is the referenced source method itself, not a
          // synthetic lambda body: its return type is what its own signature declares. Rewriting
          // it with the caller's type variable would print that variable inside a scope that
          // cannot name it.
          if (!isMethodReference() && infType != null && !infType.equals(VarType.VARTYPE_VOID)) {
            if (!curType.equals(infType) || (infType.isGeneric() && !((GenericType)infType).equalsExact(curType))) {
              GenericMethodDescriptor genDesc = new GenericMethodDescriptor(Collections.emptyList(), Collections.emptyList(), Collections.emptyList(), infType, Collections.emptyList());
              DummyExitStatement dummyExit = methodWrapper.root.getDummyExit();

              for (StatEdge edge : dummyExit.getAllPredecessorEdges()) {
                Statement source = edge.getSource();
                List<Exprent> lstExpr = source.getExprents();

                if (lstExpr != null && !lstExpr.isEmpty()) {
                  Exprent expr = lstExpr.get(lstExpr.size() - 1);
                  if (expr instanceof ExitExprent) {
                    ExitExprent ex = (ExitExprent)expr;
                    if (ex.getExitType() == ExitExprent.Type.RETURN) {
                      ex.getMethodDescriptor().genericInfo = genDesc;
                      break; // desc var should be the same for all returns
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  /** Give every return in a lambda body the functional method's recorded return type. */
  private static void applyReturnTarget(Statement stat, GenericMethodDescriptor genDesc) {
    List<Exprent> exprents = stat.getExprents();
    if (exprents != null) {
      for (Exprent exprent : exprents) {
        if (exprent instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN
          && exit.getMethodDescriptor() != null) {
          exit.getMethodDescriptor().genericInfo = genDesc;
        }
      }
    }
    for (Statement child : stat.getStats()) {
      if (child != null) {
        applyReturnTarget(child, genDesc);
      }
    }
  }

  public boolean doesClassHaveMethodsNamedSame() {
    if (this.lambda && this.methodReference) {
      ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(this.newType.value);

      if (node != null) {
        String name = node.lambdaInformation.content_method_name;
        ClassNode contentClass = DecompilerContext.getClassProcessor().getMapRootClasses().get(node.lambdaInformation.content_class_name);

        if (contentClass == null) {
          return false;
        }

        boolean foundOne = false;
        for (StructMethod method : contentClass.classStruct.getMethods()) {
          if (method.getName().equals(name)) {
            if (foundOne) {
              return true;
            } else {
              foundOne = true;
            }
          }
        }
      }
    }

    return false;
  }

  @Override
  public void replaceExprent(Exprent oldExpr, Exprent newExpr) {
    if (oldExpr == constructor) {
      constructor = (InvocationExprent)newExpr;
    }

    if (constructor != null) {
      constructor.replaceExprent(oldExpr, newExpr);
    }

    for (int i = 0; i < lstDims.size(); i++) {
      if (oldExpr == lstDims.get(i)) {
        lstDims.set(i, newExpr);
      }
    }

    for (int i = 0; i < lstArrayElements.size(); i++) {
      if (oldExpr == lstArrayElements.get(i)) {
        lstArrayElements.set(i, newExpr);
      }
    }
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof NewExprent)) return false;

    NewExprent ne = (NewExprent)o;
    return InterpreterUtil.equalObjects(newType, ne.getNewType()) &&
           InterpreterUtil.equalLists(lstDims, ne.getLstDims()) &&
           InterpreterUtil.equalObjects(constructor, ne.getConstructor()) &&
           directArrayInit == ne.directArrayInit &&
           InterpreterUtil.equalLists(lstArrayElements, ne.getLstArrayElements());
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, lstArrayElements);
    measureBytecode(values, lstDims);
    measureBytecode(values, constructor);
    measureBytecode(values);
  }

  public InvocationExprent getConstructor() {
    return constructor;
  }

  public void setConstructor(InvocationExprent constructor) {
    this.constructor = constructor;
  }

  public List<Exprent> getLstDims() {
    return lstDims;
  }

  public VarType getNewType() {
    return newType;
  }

  public List<Exprent> getLstArrayElements() {
    return lstArrayElements;
  }

  public void setLstArrayElements(List<Exprent> lstArrayElements) {
    this.lstArrayElements = lstArrayElements;
  }

  public void setDirectArrayInit(boolean directArrayInit) {
    this.directArrayInit = directArrayInit;
  }

  public boolean isDirectArrayInit() {
    return directArrayInit;
  }

  public void setVarArgParam(boolean isVarArgParam) {
    this.isVarArgParam = isVarArgParam;
  }

  public boolean isVarArgParam() {
    return this.isVarArgParam;
  }

  public boolean isLambda() {
    return lambda;
  }

  public boolean isAnonymous() {
    return anonymous;
  }

  public void setAnonymous(boolean anonymous) {
    this.anonymous = anonymous;
  }

  public boolean isEnumConst() {
    return enumConst;
  }

  public void setEnumConst(boolean enumConst) {
    this.enumConst = enumConst;
  }

  @Override
  public void setIsQualifier() {
    isQualifier = true;
  }

  /**
   * Prints the supertype an anonymous class is written against, with a diamond where javac was
   * given one.
   *
   * <p>A capturing anonymous class compiled from explicit type arguments carries a synthetic
   * constructor signature; one compiled from a diamond carries none. The class's own signature is
   * the same either way, so the constructor attribute is the only record of which form the original
   * source used, and printing the arguments where the original had a diamond adds an attribute the
   * class does not have. A class that captures nothing carries no signature in either form and is
   * left alone, since there the arguments are also recoverable from the context.
   *
   * <p>A receiver has no target type, so a diamond there cannot be inferred and cannot be the
   * form the source wrote: the explicit arguments are printed even without the constructor's
   * signature.
   */
  private void appendAnonymousSuperType(TextBuffer buf, VarType superType, ClassNode node) {
    if (superType instanceof GenericType && !((GenericType)superType).getArguments().isEmpty()
        && RoundTrip.selector("rt-diamond")
        && node.classStruct != null) {
      for (StructMethod method : node.classStruct.getMethods()) {
        if (CodeConstants.INIT_NAME.equals(method.getName()) && !method.getDescriptor().startsWith("()")) {
          if (method.getSignature() == null && !isQualifier) {
            buf.appendCastTypeName(new VarType(superType.type, superType.arrayDim, superType.value)).append("<>");
            return;
          }
          break;
        }
      }
    }
    buf.appendCastTypeName(superType);
  }

  private static boolean hasTypeParameters(VarType type) {
    if (type == null || !type.equals(VarType.VARTYPE_OBJECT)) {
      var node = DecompilerContext.getStructContext().getClass(type.value);
      return node != null && node.getSignature() != null && !node.getSignature().fparameters.isEmpty();
    }
    return false;
  }

  /**
   * Records the context target of a creation when it fixes every type parameter of the created
   * class. A creation in a field initializer, a return value or a local's initializer has no
   * target type of its own: javac types it from the surrounding declaration, so a source that
   * wrote the diamond produced the same allocation as one that named every argument. Without
   * the record the printer has no recovered argument to print and writes the raw type, which
   * changes what javac infers for the enclosing call.
   */
  private void recordExpectedCreationType(GenericClassDescriptor signature, VarType upperBound) {
    if (expectedCreationType != null || anonymous || lambda || enumConst || constructor == null
        || newType.arrayDim != 0) {
      return;
    }
    if (!(upperBound instanceof GenericType target) || target.type != CodeType.OBJECT
        || target.arrayDim != 0 || target.getWildcard() != GenericType.WILDCARD_NO
        || target.value == null || !target.isGeneric()) {
      return;
    }
    // A target a source could name. A capture or an out-of-scope variable means the target is
    // the printer's own inference rather than a type the original could have written.
    if (!nameableArrayComponent(target)) {
      return;
    }
    List<VarType> args = creationArguments(signature, target);
    if (args == null) {
      return;
    }
    expectedCreationType = target;
    expectedCreationArgs = args;
  }

  /**
   * The created class's own type parameters as the recorded target fixes them, in declaration
   * order, or null when the target leaves one of them open. A same-class target lists them
   * directly; a supertype target is projected back through the class's recorded hierarchy
   * ({@code ChunkResult<R>} is {@code Fail<R>} through {@code Fail<T> extends ChunkResult<T>}).
   */
  private List<VarType> creationArguments(GenericClassDescriptor signature, GenericType target) {
    if (target.value.equals(newType.value)) {
      List<VarType> args = target.getArguments();
      if (signature != null && args.size() != signature.fparameters.size()) {
        return null;
      }
      List<VarType> stripped = new ArrayList<>(args.size());
      for (VarType argument : args) {
        stripped.add(stripCreationWildcard(argument));
      }
      return stripped;
    }
    if (signature == null) {
      return null;
    }
    VarType view = GenericType.getGenericSuperType(signature.genericType, target);
    if (!(view instanceof GenericType viewType) || viewType.value == null
        || !viewType.value.equals(target.value)
        || viewType.getArguments().size() != target.getArguments().size()) {
      return null;
    }
    Map<VarType, VarType> solved = new HashMap<>();
    viewType.mapGenVarsTo(target, solved);
    List<VarType> args = new ArrayList<>(signature.fparameters.size());
    for (String parameter : signature.fparameters) {
      VarType variable = GenericType.parse("T" + parameter + ";");
      if (!solved.containsKey(variable)) {
        return null;
      }
      args.add(stripCreationWildcard(solved.get(variable)));
    }
    return args;
  }

  /**
   * The nameable instantiation a recorded target's variance marker stands for: the bound of a
   * bounded wildcard, and the unbounded wildcard itself when there is none. A creation's target
   * is often a called method's parameter type ({@code Map<? extends K, ? extends V>}); the
   * arguments javac infers for the diamond are the bounds, and those are what a source writes.
   */
  private static VarType stripCreationWildcard(VarType type) {
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      if (generic.value == null) {
        return null;
      }
      return stripCreationWildcard(GenericType.withWildcard(generic, GenericType.WILDCARD_NO));
    }
    return type;
  }

  /** Whether every argument a receiver's explicit type argument list would print is nameable. */
  private boolean printableCreationArguments(List<VarType> args) {
    if (args == null || args.isEmpty()) {
      return false;
    }
    for (VarType argument : args) {
      if (!nameableArrayElement(argument)) {
        return false;
      }
    }
    return true;
  }

  /**
   * The name of a non-static inner class declared inside the class being decompiled, qualified by
   * its outer type's arguments.
   *
   * <p>javac rejects type arguments written on a raw type, so a source that compiled never says
   * {@code new Outer.Inner<T>()} for a class that needs the outer's parameters; it writes
   * {@code new Outer<T>.Inner<>()}. A member class that holds an outer instance carries the
   * compiler's synthetic {@code this$0} field recording that outer, and the arguments the outer
   * needs are exactly the type parameters the current class declares.
   */
  private static String qualifiedInnerNewType(VarType type) {
    if (type == null || type.type != CodeType.OBJECT || type.arrayDim != 0 || type.isGeneric()) {
      return null;
    }
    StructClass inner = DecompilerContext.getStructContext().getClass(type.value);
    if (inner == null) {
      return null;
    }
    StructClass outer = capturedOuterClass(inner);
    if (outer == null || outer.getSignature() == null || outer.getSignature().fparameters.isEmpty()) {
      return null;
    }
    StructClass current = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS);
    String outerName = outer.qualifiedName;
    String prefix = outerName + "$";
    if (current == null || !(current.qualifiedName.equals(outerName) || current.qualifiedName.startsWith(prefix))) {
      return null;
    }
    if (type.value == null || !type.value.startsWith(prefix) || type.value.indexOf('$', prefix.length()) >= 0) {
      return null;
    }
    StringBuilder signature = new StringBuilder("L").append(outerName).append('<');
    for (String parameter : outer.getSignature().fparameters) {
      signature.append('T').append(parameter).append(';');
    }
    signature.append(">.").append(type.value.substring(prefix.length())).append(';');
    VarType view = GenericType.parse(signature.toString());
    return view.isGeneric() ? ExprProcessor.getTypeName(view) : null;
  }

  /** The outer class whose instance a member class holds in the compiler's synthetic field. */
  private static StructClass capturedOuterClass(StructClass inner) {
    for (StructField field : inner.getFields()) {
      String name = field.getName();
      if (name.startsWith("this$") && field.getDescriptor().startsWith("L") && field.getDescriptor().endsWith(";")) {
        return DecompilerContext.getStructContext().getClass(field.getDescriptor().substring(1, field.getDescriptor().length() - 1));
      }
    }
    return null;
  }

  public boolean isMethodReference() {
    return methodReference;
  }

  /**
   * Whether every return in the lambda's body is one of the lambda's own parameters, unchanged
   * (an identity function). Such a body is typed by the target that flows through its parameter,
   * so it carries no type of its own either.
   */
  public boolean returnsOnlyOwnParameters() {
    if (!lambda) {
      return false;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return false;
    }
    ClassWrapper wrapper = node.getWrapper();
    if (wrapper == null) {
      return false;
    }
    MethodWrapper mt = wrapper.getMethodWrapper(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (mt == null || mt.root == null) {
      return false;
    }
    MethodDescriptor content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
    MethodDescriptor sam = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);
    int slot = node.lambdaInformation.is_content_method_static ? 0 : 1;
    int firstParameter = content.params.length - sam.params.length;
    Set<VarVersionPair> parameters = new HashSet<>();
    for (int i = 0; i < content.params.length; i++) {
      if (i >= firstParameter) {
        parameters.add(new VarVersionPair(slot, 0));
      }
      slot += content.params[i].stackSize;
    }
    boolean any = false;
    for (StatEdge edge : mt.root.getDummyExit().getAllPredecessorEdges()) {
      List<Exprent> exprents = edge.getSource().getExprents();
      if (exprents == null || exprents.isEmpty() || !(exprents.get(exprents.size() - 1) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN) {
        continue;
      }
      Exprent value = exit.getValue();
      while (value instanceof FunctionExprent cast && cast.getFuncType() == FunctionExprent.FunctionType.CAST
        && !cast.getLstOperands().isEmpty()) {
        value = cast.getLstOperands().get(0);
      }
      if (!(value instanceof VarExprent variable) || !parameters.contains(variable.getVarVersionPair())) {
        return false;
      }
      any = true;
    }
    return any;
  }

  /**
   * Whether the lambda's body returns a functional value (a lambda or a method reference). Such a
   * body has no type of its own and can only be typed by the functional target, so the call
   * site's target must not be withheld from it.
   */
  public boolean returnsFunctionalValue() {
    if (!lambda) {
      return false;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return false;
    }
    ClassWrapper wrapper = node.getWrapper();
    if (wrapper == null) {
      return false;
    }
    MethodWrapper mt = wrapper.getMethodWrapper(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (mt == null || mt.root == null) {
      return false;
    }
    for (StatEdge edge : mt.root.getDummyExit().getAllPredecessorEdges()) {
      List<Exprent> exprents = edge.getSource().getExprents();
      if (exprents == null || exprents.isEmpty() || !(exprents.get(exprents.size() - 1) instanceof ExitExprent exit)
        || exit.getExitType() != ExitExprent.Type.RETURN) {
        continue;
      }
      Exprent value = exit.getValue();
      while (value instanceof FunctionExprent cast && cast.getFuncType() == FunctionExprent.FunctionType.CAST
        && !cast.getLstOperands().isEmpty()) {
        value = cast.getLstOperands().get(0);
      }
      if (value instanceof NewExprent created && created.isLambda()) {
        return true;
      }
    }
    return false;
  }

  /** The functional interface type this lambda was inferred against, if any. */
  public VarType getInferredLambdaType() {
    return inferredLambdaType;
  }

  /**
   * Tells this lambda whether the call site's recorded target left a SAM position captured. A
   * captured target cannot type an identity parameter: its position is an inference the source's
   * own cast is what guides.
   */
  public void setFunctionalParameterCaptured(boolean captured) {
    this.functionalParameterCaptured = captured;
  }

  /**
   * The SAM's return type as this functional argument was inferred to produce, instantiated from
   * the functional interface's recorded type. A type variable that stays unresolved here belongs
   * to the referenced class or the interface itself; print-time code cannot name it, and a
   * call's own inference cannot bind it to a type variable of the caller either.
   */
  public VarType getFunctionalReturnType() {
    if (!lambda || inferredLambdaType == null || !inferredLambdaType.isGeneric()) {
      return null;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(node.anonymousClassType.value);
    if (iface == null || iface.getSignature() == null) {
      return null;
    }
    StructMethod sam = iface.getMethod(getLambdaMethodKey());
    if (sam == null || sam.getSignature() == null || sam.getSignature().returnType == null) {
      return null;
    }
    Map<VarType, VarType> map = new HashMap<>();
    iface.getSignature().genericType.mapGenVarsTo((GenericType) inferredLambdaType, map);
    return sam.getSignature().returnType.remap(map);
  }

  /**
   * The SAM's parameter types as this functional argument was inferred against, instantiated
   * from the functional interface's recorded type. A lambda's own parameters carry no written
   * type: the functional target fixes them, and the synthetic method only records the erased
   * descriptor. A wildcard in a parameter position is the capture an implicit parameter stands
   * for; the type the source could name is its bound.
   */
  public List<VarType> getFunctionalParameterTypes() {
    if (!lambda || inferredLambdaType == null) {
      return null;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(node.anonymousClassType.value);
    if (iface == null) {
      return null;
    }
    StructMethod sam = iface.getMethod(getLambdaMethodKey());
    if (sam == null) {
      return null;
    }
    List<VarType> parameters;
    if (sam.getSignature() != null) {
      parameters = sam.getSignature().parameterTypes;
    } else {
      parameters = Arrays.asList(MethodDescriptor.parseDescriptor(sam.getDescriptor()).params);
    }
    Map<VarType, VarType> map = null;
    if (inferredLambdaType.isGeneric()) {
      if (iface.getSignature() == null) {
        return null;
      }
      map = new HashMap<>();
      iface.getSignature().genericType.mapGenVarsTo((GenericType) inferredLambdaType, map);
    }
    // A type variable that is both the parameter and the return type is the inference variable
    // a value-preserving lambda fixes from its target; pinning it here would decide the very
    // inference the source's own cast may have been written to guide.
    VarType samReturn = sam.getSignature() != null && sam.getSignature().returnType != null
      ? sam.getSignature().returnType
      : MethodDescriptor.parseDescriptor(sam.getDescriptor()).ret;
    if (map != null) {
      samReturn = samReturn.remap(map);
    }
    if (samReturn instanceof GenericType returnWildcard && returnWildcard.getWildcard() != GenericType.WILDCARD_NO) {
      samReturn = GenericType.withWildcard(returnWildcard, GenericType.WILDCARD_NO);
    }
    List<VarType> types = new ArrayList<>();
    for (VarType parameter : parameters) {
      VarType resolved = map == null ? parameter : parameter.remap(map);
      if (resolved instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
        resolved = GenericType.withWildcard(generic, GenericType.WILDCARD_NO);
      }
      // A lower-bounded wildcard deeper in the parameter type is a capture our inference left
      // where javac solved the variable to the bound itself (List<? super S> against a value
      // the call instantiates with List<S>). The bound is what types the body.
      resolved = unwrapLowerBounds(resolved);
      // Only a type the source could name may stand for the parameter: a variable the target
      // left open, or a wildcard, is the inference's own capture and pinning it would change
      // what the target infers from the body. A variable that is both the parameter and the
      // return is the inference an identity lambda fixes from its target; it is typed only where
      // the call site's recorded target proves that position is not a capture.
      boolean inferenceVariable = resolved != null && resolved.type == CodeType.GENVAR
        && samReturn != null && samReturn.type == CodeType.GENVAR
        && resolved.value != null && resolved.value.equals(samReturn.value)
        && functionalParameterCaptured;
      types.add(!inferenceVariable && resolved != null && nameableLambdaParameterType(resolved) ? resolved : null);
    }
    return types;
  }

  /**
   * The receiver a no-bound instance reference's first SAM parameter stands for: the parameter
   * type is often the wildcard form the functional interface declares ({@code ? super X}), and
   * the value the reference accepts there is the bound itself.
   */
  private static VarType stripReferenceWildcard(VarType type) {
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return GenericType.withWildcard(generic, GenericType.WILDCARD_NO);
    }
    return type;
  }

  /**
   * Replaces every {@code ? super X} inside a lambda parameter type with its bound X, or null
   * when an unbounded wildcard leaves no nameable form. An upper-bounded wildcard is left as
   * the target recorded it.
   */
  private static VarType unwrapLowerBounds(VarType type) {
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() == GenericType.WILDCARD_SUPER) {
        return generic.value == null ? null
          : unwrapLowerBounds(GenericType.withWildcard(generic, GenericType.WILDCARD_NO));
      }
      if (generic.getArguments().isEmpty()) {
        return type;
      }
      List<VarType> arguments = new ArrayList<>(generic.getArguments().size());
      boolean changed = false;
      for (VarType argument : generic.getArguments()) {
        if (argument == null) {
          arguments.add(null);
          continue;
        }
        VarType unwrapped = unwrapLowerBounds(argument);
        if (unwrapped == null) {
          return null;
        }
        if (unwrapped != argument) {
          changed = true;
        }
        arguments.add(unwrapped);
      }
      return changed
        ? new GenericType(generic.type, generic.arrayDim, generic.value, generic.getParent(), arguments, generic.getWildcard())
        : type;
    }
    return type;
  }

  /**
   * Records the component of the context's target when it names the same class at the same array
   * depth as this creation and every type argument is nameable at the print site. A later call
   * with an unrelated bound (a raw {@code Object[]}, a target inferred from the creation itself)
   * leaves a recorded component in place.
   */
  private boolean recordArrayComponent(VarType upperBound) {
    // A varargs call's array is the compiler's: the source wrote the elements, and the class
    // file records the same allocation either way. A bare initializer names the component on
    // its declaration, never on the creation.
    if (isVarArgParam) {
      return false;
    }
    if (!directArrayInit && newType.arrayDim > 0 && upperBound instanceof GenericType target
      && target.type == CodeType.OBJECT && target.arrayDim == newType.arrayDim
      && target.value != null && target.value.equals(newType.value)
      && target.getWildcard() == GenericType.WILDCARD_NO && nameableArrayComponent(target)) {
      arrayComponentTarget = target.resizeArrayDim(0);
      return true;
    }
    return recordTypeVariableArrayComponent(upperBound);
  }

  /**
   * The component of an array the context types as a type variable's array: the instruction names
   * only the erased class, and the variable's recorded bound erases to exactly that class. A
   * source cannot write a concrete instantiation there (a generic array creation is legal only
   * over a reifiable component) and a bare class name would be a raw type, so the only form the
   * source could name is the all-wildcard one, which the recorded target cannot spell.
   */
  private boolean recordTypeVariableArrayComponent(VarType upperBound) {
    if (newType.arrayDim == 0 || upperBound == null || upperBound.arrayDim != newType.arrayDim
      || upperBound.type != CodeType.GENVAR) {
      return false;
    }
    VarType variable = upperBound.resizeArrayDim(0);
    Map<VarType, List<VarType>> named = getNamedGenerics();
    if (!Exprent.isTypeVariableNameable(variable, named)) {
      return false;
    }
    List<VarType> bounds = named.get(variable);
    if (bounds == null || bounds.isEmpty()) {
      return false;
    }
    // The erasure of a type variable is its first bound: the class bound, or the first interface
    // bound when the class bound is empty.
    VarType bound = bounds.get(0);
    if (bound == null || bound.type != CodeType.OBJECT || bound.arrayDim != 0
      || bound.value == null || !bound.value.equals(newType.value)) {
      return false;
    }
    StructClass node = DecompilerContext.getStructContext().getClass(newType.value);
    if (node == null || node.getSignature() == null || node.getSignature().fparameters.isEmpty()) {
      return false;
    }
    List<VarType> arguments = new ArrayList<>(node.getSignature().fparameters.size());
    for (int i = 0; i < node.getSignature().fparameters.size(); i++) {
      arguments.add(null); // the unbounded wildcard
    }
    arrayComponentTarget = new GenericType(CodeType.OBJECT, 0, newType.value, null, arguments,
      GenericType.WILDCARD_NO);
    return true;
  }

  /**
   * A recorded type a source could name: an unbounded wildcard may stand for an unknown
   * argument. A bare generic class is a raw type, which is a name but not one this printer may
   * invent.
   */
  private boolean nameableArrayComponent(VarType type) {
    if (type == null) {
      return true; // an unbounded wildcard argument
    }
    if (type.type == CodeType.GENVAR) {
      return Exprent.isTypeVariableNameable(type.resizeArrayDim(0), getNamedGenerics());
    }
    if (type.type != CodeType.OBJECT || type.value == null) {
      return false;
    }
    if (type instanceof GenericType generic) {
      if (generic.getParent() != null && !nameableArrayComponent(generic.getParent())) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (!nameableArrayComponent(argument)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * The component text this creation prints: the recorded target as written when it is a
   * reifiable type (every argument an unbounded wildcard, as in {@code new X<?>[]}), otherwise
   * the all-wildcard form of that component, the only parameterized array creation a source can
   * write when the target's arguments are concrete.
   */
  private VarType printedArrayComponent() {
    if (arrayComponentTarget == null) {
      return null;
    }
    return reifiableArrayComponent(arrayComponentTarget)
      ? arrayComponentTarget : wildcardArrayComponent(arrayComponentTarget);
  }

  /** Whether an array of this type is a legal creation: every argument, at every level, is `?`. */
  private static boolean reifiableArrayComponent(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return true;
    }
    if (generic.type != CodeType.OBJECT || generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    if (generic.getParent() != null && !reifiableArrayComponent(generic.getParent())) {
      return false;
    }
    for (VarType argument : generic.getArguments()) {
      if (argument != null) {
        return false;
      }
    }
    return true;
  }

  /** The same component with every type argument replaced by the unbounded wildcard. */
  private static VarType wildcardArrayComponent(VarType type) {
    if (!(type instanceof GenericType generic)) {
      return type;
    }
    VarType parent = generic.getParent() == null ? null : wildcardArrayComponent(generic.getParent());
    List<VarType> arguments;
    if (generic.getArguments().isEmpty()) {
      arguments = Collections.emptyList();
    } else {
      arguments = new ArrayList<>(generic.getArguments().size());
      for (int i = 0; i < generic.getArguments().size(); i++) {
        arguments.add(null);
      }
    }
    return new GenericType(generic.type, generic.arrayDim, generic.value, parent, arguments, generic.getWildcard());
  }

  /**
   * Whether this creation printed the all-wildcard form of a component the recorded target names
   * with type arguments: {@code new X<?>[...]} for a target {@code X<A>[]}. The printed array's
   * element type is then not assignable to the target, so the source cast the creation.
   */
  public boolean printsWildcardArrayComponentFor(VarType target) {
    if (arrayComponentTarget == null || reifiableArrayComponent(arrayComponentTarget)
      || isVarArgParam || directArrayInit) {
      return false;
    }
    return target instanceof GenericType generic && generic.type == CodeType.OBJECT
      && generic.value != null && generic.value.equals(newType.value)
      && generic.arrayDim == newType.arrayDim && generic.arrayDim > 0;
  }

  /**
   * The component type of an array whose elements all record the same parameterized instance of
   * the component class, or null when they do not agree or the instantiation cannot be named.
   */
  private VarType genericArrayComponent() {
    if (lstArrayElements.isEmpty()) {
      return null;
    }
    VarType first = lstArrayElements.get(0).getInferredExprType(null);
    if (first == null || first.type != CodeType.OBJECT || first.arrayDim != 0 || !first.isGeneric()
      || first.value == null || !first.value.equals(newType.value) || !nameableArrayElement(first)) {
      return null;
    }
    for (int i = 1; i < lstArrayElements.size(); ++i) {
      if (!FunctionExprent.sameType(lstArrayElements.get(i).getInferredExprType(null), first)) {
        return null;
      }
    }
    return first;
  }

  /** A recorded type a source could name: no wildcard, raw argument or out-of-scope variable. */
  private boolean nameableArrayElement(VarType type) {
    if (type == null) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return Exprent.isTypeVariableNameable(type.resizeArrayDim(0), getNamedGenerics());
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      if (generic.getArguments().isEmpty() && generic.value != null) {
        StructClass cls = DecompilerContext.getStructContext().getClass(generic.value);
        if (cls != null && cls.getSignature() != null && !cls.getSignature().fparameters.isEmpty()) {
          return false;
        }
      }
      for (VarType argument : generic.getArguments()) {
        if (argument == null || !nameableArrayElement(argument)) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean nameableLambdaParameterType(VarType type) {
    if (type == null || type.type == CodeType.VOID || type.type == CodeType.UNKNOWN) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return nameableTypeVariable(type.value);
    }
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return false;
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      if (generic.getArguments().isEmpty() && generic.value != null) {
        // A parameterized class written bare is a raw form: the target's capture left the
        // arguments unbound, and the source's own unchecked conversion lives in the body.
        StructClass cls = DecompilerContext.getStructContext().getClass(generic.value);
        if (cls != null && cls.getSignature() != null && !cls.getSignature().fparameters.isEmpty()) {
          return false;
        }
      }
      for (VarType argument : generic.getArguments()) {
        // A null argument is the unbounded wildcard `?`: a capture no source can name.
        if (argument == null || !nameableLambdaParameterType(argument)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Whether a type variable of this name is in scope at the print site. The full scope rules
   * hold here too: a lambda's synthetic method is static, but its source text sits in the
   * enclosing method, whose type parameters are exactly the ones the body can name.
   */
  private static boolean nameableTypeVariable(String name) {
    if (name == null || name.isEmpty()) {
      return false;
    }
    return isInScopeTypeVariable(GenericType.parse("T" + name + ";"), contextNamedGenerics());
  }

  /**
   * The arguments of a diamond whose recorded target is a parameterized supertype of the
   * constructed class ({@code new C<>()} where the target is {@code Map<List<Runnable>>}):
   * reading the target through the class's recorded supertype signature (C<K,V> as Map<K,V>)
   * solves the class's variables. The erased constructor invocation is the one the target
   * recorded, and the source named the arguments the target required.
   */
  private List<VarType> impliedArguments(VarType upperBound) {
    if (!(upperBound instanceof GenericType target) || target.type != CodeType.OBJECT
      || target.arrayDim != 0 || target.getWildcard() != GenericType.WILDCARD_NO) {
      return null;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(newType.value);
    if (cls == null || cls.getSignature() == null) {
      return null;
    }
    GenericClassDescriptor signature = cls.getSignature();
    if (signature.fparameters.isEmpty()) {
      return null;
    }
    VarType view = target.value.equals(newType.value)
      ? signature.genericType : GenericType.getGenericSuperType(signature.genericType, target);
    if (!(view instanceof GenericType superView) || !target.value.equals(superView.value)
      || superView.getArguments().size() != target.getArguments().size()) {
      return null;
    }
    Map<VarType, VarType> solved = new HashMap<>();
    superView.mapGenVarsTo(target, solved);
    List<VarType> args = new ArrayList<>(signature.fparameters.size());
    for (String parameter : signature.fparameters) {
      VarType value = solved.get(GenericType.parse("T" + parameter + ";"));
      if (!isImpliedType(value)) {
        return null;
      }
      args.add(value);
    }
    return args;
  }

  /** A type the implied arguments can name: no free variable, wildcard or raw generic. */
  private static boolean isImpliedType(VarType type) {
    if (type == null || type == GenericType.DUMMY_VAR || type.type == CodeType.GENVAR) {
      return false;
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (!isImpliedType(argument)) {
          return false;
        }
      }
      return true;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(type.value);
    return cls == null || cls.getSignature() == null || cls.getSignature().fparameters.isEmpty();
  }

  /**
   * The recovered constructor arguments do not satisfy the expected type at an invariant
   * position, but they are subtypes of the expected ones and the constructor takes the class's
   * own type variables: only a diamond lets javac infer the expected arguments from the target.
   */
  private boolean expectsWiderArguments(VarType upperBound) {
    if (!RoundTrip.selector("rt-diamond") || constructor == null
      || !(upperBound instanceof GenericType target) || target.type != CodeType.OBJECT
      || target.arrayDim != 0 || target.getWildcard() != GenericType.WILDCARD_NO
      || !target.value.equals(newType.value)) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(newType.value);
    if (cls == null || cls.getSignature() == null) {
      return false;
    }
    GenericClassDescriptor signature = cls.getSignature();
    List<VarType> targetArgs = target.getArguments();
    if (targetArgs.size() != signature.fparameters.size()) {
      return false;
    }
    StructMethod desc = constructor.getDesc();
    if (desc == null) {
      return false;
    }
    if (desc.getSignature() != null && desc.getSignature().parameterTypes.size() == signature.fparameters.size()) {
      // The constructor's own Signature names the class's variables: a diamond can infer them.
      for (String fp : signature.fparameters) {
        boolean present = false;
        for (VarType parameter : desc.getSignature().parameterTypes) {
          if (parameter != null && parameter.type == CodeType.GENVAR && parameter.arrayDim == 0
            && parameter.value.equals(fp)) {
            present = true;
          }
        }
        if (!present) {
          return false;
        }
      }
    } else {
      // No constructor Signature: the erased parameters must still be the class's variables'
      // bounds, in order, for the target to drive inference through them.
      VarType[] parameters = MethodDescriptor.parseDescriptor(desc.getDescriptor()).params;
      if (parameters.length != signature.fparameters.size()) {
        return false;
      }
      for (int i = 0; i < parameters.length; i++) {
        List<VarType> declared = i < signature.fbounds.size() ? signature.fbounds.get(i) : null;
        VarType bound = declared == null || declared.isEmpty() || declared.get(0).type == CodeType.GENVAR
          ? VarType.VARTYPE_OBJECT : declared.get(0);
        if (bound.type == CodeType.OBJECT) {
          if (!parameters[i].equals(VarType.VARTYPE_OBJECT)) {
            return false;
          }
        } else if (!parameters[i].equals(new VarType(bound.type, bound.arrayDim, bound.value))) {
          return false;
        }
      }
    }
    List<VarType> recovered = constructor.getGenericArgs();
    if (recovered.size() != targetArgs.size()) {
      return false;
    }
    boolean differs = false;
    for (int i = 0; i < recovered.size(); i++) {
      VarType mine = recovered.get(i);
      VarType want = targetArgs.get(i);
      if (mine == null || want == null) {
        return false;
      }
      if (mine.type == CodeType.GENVAR || want.type == CodeType.GENVAR) {
        if (mine.equals(want)) {
          continue;
        }
        return false;
      }
      if (mine.type != CodeType.OBJECT || want.type != CodeType.OBJECT) {
        return false;
      }
      if (sameDiamondType(mine, want)) {
        continue;
      }
      if (!DecompilerContext.getStructContext().instanceOf(mine.value, want.value)) {
        return false;
      }
      differs = true;
    }
    return differs;
  }

  private static boolean sameDiamondType(VarType a, VarType b) {
    if (a instanceof GenericType generic) {
      return generic.equalsExact(b);
    }
    return b != null && !(b instanceof GenericType) && a.equals(b);
  }

  /**
   * A bound method reference's recorded instantiated type proves the receiver's parameterized
   * type. The metafactory's instantiated method type is the functional method javac adapted, and
   * when its return type is a class but the referenced method's erased return is Object while its
   * generic signature returns the receiver class's own sole type variable, the only way javac
   * produced that adaptation is a receiver typed {@code C<Return>}: the variable had to be bound
   * to the recorded return type. The receiver expression is printed as the reference's qualifier,
   * and a diamond constructor inside it is the element that carried the type argument in source;
   * printing the recorded argument there keeps javac's inference of the constructor from closing
   * on Object and rejecting the reference. Nothing is forced unless every recorded fact agrees.
   */

  private void forceRecordedReceiverType(Exprent receiver) {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null || !node.lambdaInformation.is_method_reference
      || node.lambdaInformation.is_content_method_static) {
      return;
    }
    MethodDescriptor sam = MethodDescriptor.parseDescriptor(node.lambdaInformation.method_descriptor);
    MethodDescriptor content = MethodDescriptor.parseDescriptor(node.lambdaInformation.content_method_descriptor);
    VarType samReturn = sam.ret;
    if (samReturn.type != CodeType.OBJECT || samReturn.arrayDim != 0
      || samReturn.value.equals(content.ret.value)) {
      return;
    }
    StructClass receiverClass = DecompilerContext.getStructContext().getClass(node.lambdaInformation.content_class_name);
    if (receiverClass == null || receiverClass.getSignature() == null
      || receiverClass.getSignature().fparameters.size() != 1) {
      return;
    }
    StructMethod referenced = receiverClass.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    if (referenced == null || referenced.getSignature() == null) {
      return;
    }
    VarType declared = referenced.getSignature().returnType;
    if (declared == null || declared.type != CodeType.GENVAR
      || !declared.value.equals(receiverClass.getSignature().fparameters.get(0))) {
      return;
    }
    for (Exprent expr : receiver.getAllExprents(true, true)) {
      if (expr instanceof NewExprent created && created != this && !created.isLambda() && !created.isAnonymous()
        && created.newType.type == CodeType.OBJECT && created.newType.arrayDim == 0
        && created.newType.value.equals(receiverClass.qualifiedName) && created.constructor != null) {
        created.forcedConstructorArgs = new ArrayList<>(List.of(samReturn));
        return;
      }
    }
  }

  /**
   * The instantiated class a static, constructor or unbound instance method reference names, when
   * the recorded types prove the source pinned its type arguments. The printer's inference took the value's
   * type from the target (a recorded signature); javac types a method reference without the
   * target of the chain it is passed into, and a type variable no constructor argument constrains
   * then defaults to its declared bound. The qualifier is printed only when the recorded
   * instantiation names a type variable that is in scope and is not that bound.
   */
  private VarType methodReferenceQualifier() {
    if (!RoundTrip.selector("rt-demand-witness")
      || !lambda || !isMethodReference() || inferredLambdaType == null || !inferredLambdaType.isGeneric()) {
      return null;
    }
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node == null || node.lambdaInformation == null) {
      return null;
    }
    // A static method or a constructor names its class as the reference's qualifier; an unbound
    // instance method names the class of the receiver it takes as the first SAM parameter.
    boolean isConstructor = CodeConstants.INIT_NAME.equals(node.lambdaInformation.content_method_name);
    boolean unboundInstance = !node.lambdaInformation.is_content_method_static && !isConstructor
      && (constructor == null || constructor.getInstance() == null);
    if (!node.lambdaInformation.is_content_method_static && !isConstructor && !unboundInstance) {
      return null;
    }
    String contentClass = node.lambdaInformation.content_class_name;
    StructClass target = DecompilerContext.getStructContext().getClass(contentClass);
    if (target == null || target.getSignature() == null || target.getSignature().fparameters.isEmpty()) {
      return null;
    }
    // A class type variable the reference's own parameters mention is inferred by javac from the
    // arguments; naming it on the qualifier would contradict that inference.
    StructMethod content = target.getMethod(node.lambdaInformation.content_method_name,
      node.lambdaInformation.content_method_descriptor);
    Set<String> fromArguments = new HashSet<>();
    if (content != null && content.getSignature() != null) {
      for (VarType parameter : content.getSignature().parameterTypes) {
        collectTypeVariableNames(parameter, fromArguments);
      }
    }
    StructClass iface = DecompilerContext.getStructContext().getClass(node.anonymousClassType.value);
    if (iface == null || iface.getSignature() == null) {
      return null;
    }
    StructMethod sam = iface.getMethod(getLambdaMethodKey());
    if (sam == null || sam.getSignature() == null || sam.getSignature().returnType == null) {
      return null;
    }
    // A functional interface with no parameters gives javac nothing but the target to infer the
    // reference's type arguments from; naming our own inference there pins whatever the printer
    // happened to compute (ArrayList<E>::new where the stream's element type is what the
    // collection must hold, and E belongs to the enclosing class).
    if (sam.getSignature().parameterTypes.isEmpty()) {
      return null;
    }
    Map<VarType, VarType> map = new HashMap<>();
    iface.getSignature().genericType.mapGenVarsTo((GenericType) inferredLambdaType, map);
    VarType produced;
    if (unboundInstance) {
      // The receiver an unbound instance reference takes as its first SAM parameter is the
      // class the qualifier names, and the recorded instantiation is the one javac infers
      // for the source's `Type<...>::method`.
      if (content == null || content.getSignature() == null
        || content.getSignature().parameterTypes.size() + 1 != sam.getSignature().parameterTypes.size()) {
        return null;
      }
      produced = unwrapWildcard(sam.getSignature().parameterTypes.get(0).remap(map));
    } else {
      produced = unwrapWildcard(sam.getSignature().returnType.remap(map));
    }
    if (produced == null || produced.type != CodeType.OBJECT || !produced.isGeneric()
      || !contentClass.equals(produced.value)) {
      return null;
    }
    GenericClassDescriptor signature = target.getSignature();
    List<VarType> args = ((GenericType) produced).getArguments();
    if (args.size() != signature.fparameters.size()) {
      return null;
    }
    Map<VarType, List<VarType>> named = getNamedGenerics();
    boolean pinned = false;
    for (int i = 0; i < args.size(); i++) {
      VarType arg = args.get(i);
      if (!isReferenceArgument(arg, named)) {
        return null;
      }
      if (fromArguments.contains(signature.fparameters.get(i))) {
        return null;
      }
      List<VarType> declared = signature.fbounds.size() > i ? signature.fbounds.get(i) : null;
      VarType bound = declared == null || declared.isEmpty() ? null : declared.get(0);
      if (isInScopeTypeVariable(arg, named)
        && (bound == null || bound.type != CodeType.GENVAR || !bound.value.equals(arg.value))) {
        pinned = true;
      }
    }
    return pinned ? produced : null;
  }

  /** The names of every type variable mentioned in a recorded type. */
  private static void collectTypeVariableNames(VarType type, Set<String> names) {
    if (type == null) {
      return;
    }
    if (type.type == CodeType.GENVAR) {
      names.add(type.value);
    }
    if (type instanceof GenericType generic) {
      for (VarType argument : generic.getArguments()) {
        collectTypeVariableNames(argument, names);
      }
    }
  }

  /** Strip a wildcard wrapper to the type it bounds; other types are returned unchanged. */
  private static VarType stripWildcard(VarType type) {
    if (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      return GenericType.withWildcard(generic, GenericType.WILDCARD_NO);
    }
    return type;
  }

  /** Strip the wildcards a functional interface's return position wraps a value in. */
  private static VarType unwrapWildcard(VarType type) {
    while (type instanceof GenericType generic && generic.getWildcard() != GenericType.WILDCARD_NO) {
      List<VarType> arguments = generic.getArguments();
      if (arguments.size() != 1 || arguments.get(0) == null) {
        return null;
      }
      type = arguments.get(0);
    }
    return type;
  }

  /** A type argument a source can write: an in-scope type variable or a printable generic type. */
  private static boolean isReferenceArgument(VarType type, Map<VarType, List<VarType>> named) {
    if (type == null || type == GenericType.DUMMY_VAR) {
      return false;
    }
    if (type.type == CodeType.GENVAR) {
      return isInScopeTypeVariable(type, named);
    }
    if (type instanceof GenericType generic) {
      if (generic.getWildcard() != GenericType.WILDCARD_NO) {
        return false;
      }
      for (VarType argument : generic.getArguments()) {
        if (argument != null && !isReferenceArgument(argument, named)) {
          return false;
        }
      }
      return !generic.getArguments().isEmpty() || !hasTypeParameters(type);
    }
    return type.type == CodeType.OBJECT;
  }

  public String getLambdaMethodKey() {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node != null && constructor != null) {
      String descriptor = ((PrimitiveConstant)constructor.getBootstrapArguments().get(0)).getString();
      return InterpreterUtil.makeUniqueKey(node.lambdaInformation.method_name, descriptor);
    }
    return "";
  }


  public String getLambdaContentMethodKey() {
    ClassNode node = DecompilerContext.getClassProcessor().getMapRootClasses().get(newType.value);
    if (node != null && constructor != null) {
      return InterpreterUtil.makeUniqueKey(node.lambdaInformation.content_method_name, node.lambdaInformation.content_method_descriptor);
    }
    return "";
  }

  public void setInvocationInstance() {
    if (constructor != null) {
      constructor.setInvocationInstance();
    }
  }

  @Override
  public void processSforms(SFormsConstructor sFormsConstructor, VarMapHolder varMaps, Statement stat, boolean calcLiveVars) {
    super.processSforms(sFormsConstructor, varMaps, stat, calcLiveVars);

    if (sFormsConstructor.trackFieldVars && this.getNewType().type == CodeType.OBJECT) {
      varMaps.getNormal().removeAllFields();
    }
  }
}
