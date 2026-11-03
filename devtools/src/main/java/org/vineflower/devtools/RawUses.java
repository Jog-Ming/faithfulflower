package org.vineflower.devtools;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.InstanceOfTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewArrayTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.util.JavacTask;
import com.sun.source.util.TreePath;
import com.sun.source.util.TreePathScanner;
import com.sun.source.util.Trees;

import javax.lang.model.element.Element;
import javax.lang.model.element.TypeElement;
import javax.lang.model.type.ArrayType;
import javax.lang.model.type.DeclaredType;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.type.WildcardType;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Counts raw uses of parameterized types in a source file: a written type whose class declares
 * type parameters but supplies none, in a declaration, cast, instanceof test, creation, array or
 * explicit type argument. A method reference's qualifier is left out: it is a poly expression
 * whose receiver type comes from the target, and javac does not report it as a raw use either.
 *
 * <p>javac has no warning for a raw cast: the cast is reifiable and therefore a checked operation,
 * so neither {@code -Xlint:rawtypes} nor {@code -Xlint:unchecked} reports it. This scanner walks
 * the attributed trees instead, which is the check an IDE performs, and counts every written raw
 * type once.
 */
public final class RawUses {
  public record Site(String file, long line, String type) {
  }

  public record Result(int count, List<Site> sites) {
    public static final Result EMPTY = new Result(0, List.of());
  }

  private RawUses() {
  }

  /** Parses and attributes the task's sources, then counts the raw uses. */
  public static Result analyze(JavacTask task) throws IOException {
    Trees trees = Trees.instance(task);
    Iterable<? extends CompilationUnitTree> units = task.parse();
    task.analyze();
    List<Site> sites = new ArrayList<>();
    for (CompilationUnitTree unit : units) {
      new Scanner(trees, unit, sites).scan(unit, null);
    }
    return new Result(sites.size(), sites);
  }

  private static final class Scanner extends TreePathScanner<Void, Void> {
    private final Trees trees;
    private final CompilationUnitTree unit;
    private final List<Site> sites;
    private final Set<String> seen = new HashSet<>();

    Scanner(Trees trees, CompilationUnitTree unit, List<Site> sites) {
      this.trees = trees;
      this.unit = unit;
      this.sites = sites;
    }

    @Override
    public Void visitVariable(VariableTree node, Void unused) {
      check(node.getType());
      return super.visitVariable(node, unused);
    }

    @Override
    public Void visitMethod(MethodTree node, Void unused) {
      check(node.getReturnType());
      for (Tree thrown : node.getThrows()) {
        check(thrown);
      }
      return super.visitMethod(node, unused);
    }

    @Override
    public Void visitClass(ClassTree node, Void unused) {
      check(node.getExtendsClause());
      for (Tree implemented : node.getImplementsClause()) {
        check(implemented);
      }
      for (Tree permitted : node.getPermitsClause()) {
        check(permitted);
      }
      return super.visitClass(node, unused);
    }

    @Override
    public Void visitTypeParameter(TypeParameterTree node, Void unused) {
      for (Tree bound : node.getBounds()) {
        check(bound);
      }
      return super.visitTypeParameter(node, unused);
    }

    @Override
    public Void visitTypeCast(TypeCastTree node, Void unused) {
      check(node.getType());
      return super.visitTypeCast(node, unused);
    }

    @Override
    public Void visitInstanceOf(InstanceOfTree node, Void unused) {
      check(node.getType());
      return super.visitInstanceOf(node, unused);
    }

    @Override
    public Void visitNewClass(NewClassTree node, Void unused) {
      // A diamond or explicit type arguments are a parameterized creation; the identifier's
      // mirror may then still be raw for a nested class, which the recursive check sees.
      if (!(node.getIdentifier() instanceof ParameterizedTypeTree)) {
        check(node.getIdentifier());
      }
      return super.visitNewClass(node, unused);
    }

    @Override
    public Void visitNewArray(NewArrayTree node, Void unused) {
      check(node.getType());
      return super.visitNewArray(node, unused);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void unused) {
      for (Tree argument : node.getTypeArguments()) {
        check(argument);
      }
      return super.visitMethodInvocation(node, unused);
    }

    private void check(Tree typeTree) {
      if (typeTree == null) {
        return;
      }
      TypeMirror mirror;
      try {
        mirror = trees.getTypeMirror(new TreePath(getCurrentPath(), typeTree));
      } catch (RuntimeException ignored) {
        return;
      }
      if (mirror != null) {
        count(mirror, typeTree);
      }
    }

    private void count(TypeMirror type, Tree where) {
      switch (type.getKind()) {
        case DECLARED -> {
          DeclaredType declared = (DeclaredType) type;
          Element element = declared.asElement();
          if (element instanceof TypeElement owner && !owner.getTypeParameters().isEmpty()
            && declared.getTypeArguments().isEmpty()) {
            long position = trees.getSourcePositions().getStartPosition(unit, where);
            long line = position < 0 ? -1 : unit.getLineMap().getLineNumber(position);
            // A pattern variable carries the same type tree as its instanceof test; count the
            // written type once.
            if (seen.add(position + "|" + owner.getQualifiedName())) {
              sites.add(new Site(unit.getSourceFile().getName(), line,
                owner.getQualifiedName().toString()));
            }
          }
          TypeMirror enclosing = declared.getEnclosingType();
          if (enclosing != null && enclosing.getKind() != TypeKind.NONE) {
            count(enclosing, where);
          }
          for (TypeMirror argument : declared.getTypeArguments()) {
            count(argument, where);
          }
        }
        case ARRAY -> count(((ArrayType) type).getComponentType(), where);
        case WILDCARD -> {
          WildcardType wildcard = (WildcardType) type;
          if (wildcard.getExtendsBound() != null) {
            count(wildcard.getExtendsBound(), where);
          }
          if (wildcard.getSuperBound() != null) {
            count(wildcard.getSuperBound(), where);
          }
        }
        default -> {
        }
      }
    }
  }
}
