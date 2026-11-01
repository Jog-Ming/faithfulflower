// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.collectors.BytecodeMappingTracer;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.StructRecordComponent;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructLineNumberTableAttribute;
import org.jetbrains.java.decompiler.util.Pair;
import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Moves the printed source onto the original's line numbers without compiling.
 *
 * <p>The printer already records, for every bytecode offset, the line it printed that instruction
 * on, and the class being decompiled carries the original LineNumberTable. Comparing the two gives
 * one constraint per entry: this printed line must move to that original line. Blank padding lines
 * shift the following text down; blank or padding lines that carry no entry at all can be deleted or
 * joined onto the line above, shifting the text up. A line whose two entries want different shifts
 * is left alone, and a shift that cannot be paid in full is paid in part, so one stubborn method
 * does not cost the file every other alignment.
 */
public final class LineAlign {
  /**
   * A blank line. Padding must not invent a comment: the source's own comments are unknown, and a
   * comment line is a claim about text the class file does not record. A blank line shifts the
   * following lines exactly the same way.
   */
  static final String PADDING = "";
  private static final java.util.Set<String> DECLARATION_MODIFIERS = java.util.Set.of(
    "public", "protected", "private", "static", "final", "abstract", "strictfp",
    "sealed", "non-sealed");
  private static final String[][] RECORD_MEMBERS = {
    {"hashCode", "()I"},
    {"equals", "(Ljava/lang/Object;)Z"},
    {"toString", "()Ljava/lang/String;"},
  };
  private static final boolean debug = System.getenv("NEUROFLOWER_LINEALIGN_DEBUG") != null;

  private LineAlign() {
  }

  /** The aligned text, or null when the buffer cannot be aligned and must be left as printed. */
  public static String align(TextBuffer buffer, ClassesProcessor.ClassNode root) {
    String text = buffer.convertToStringAndAllowDataDiscard();
    if (RoundTrip.selector("rt-constant-sites")) {
      try {
        // Runs on the printed text before any line edit, so the bytecode positions the buffer
        // recorded still describe this string. The switch replaces the whole-file constant pass.
        text = ConstantNames.restore(text, root, buffer.getBytecodePositions(),
          buffer.getClassRegions());
      }
      catch (RuntimeException e) {
        // A class must not be lost because its constant sites could not be classified.
      }
    }
    String separator = DecompilerContext.getNewLineSeparator();
    String[] lines = text.split(java.util.regex.Pattern.quote(separator), -1);

    Map<Pair<String, String>, BytecodeMappingTracer> tracers;
    try {
      tracers = buffer.getTracers();
    } catch (RuntimeException e) {
      return null;
    }
    applyFieldDeclarationAnchors(tracers);

    if (RoundTrip.selector("rt-same-line-join")) {
      String joined = joinSameTargetLines(text, separator, lines, tracers, lineRecords(tracers, lines));
      if (joined != null) {
        text = joined;
        lines = text.split(java.util.regex.Pattern.quote(separator), -1);
      }
    }
    LineRecords records = lineRecords(tracers, lines);

    boolean gapAlign = RoundTrip.selector("rt-gap-align");
    TreeMap<Integer, Integer> shifts = new TreeMap<>();
    Set<Integer> conflicted = new HashSet<>();
    Set<Integer> unmergeable = new HashSet<>();
    Set<Integer> inherited = new HashSet<>();
    Set<Integer> entryLines = new HashSet<>();
    Set<Integer> joinBlocked = new HashSet<>();
    Map<Integer, List<int[]>> candidates = new TreeMap<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      String className = tracerEntry.getKey().a;
      String methodKey = tracerEntry.getKey().b;
      Map<Integer, Integer> mapping = tracerEntry.getValue().getMapping();
      if (methodKey.startsWith("<field-init ")) {
        // The initializer was lifted out of one constructor, whose table places each declaration
        // separately; only when the decompiler no longer knows that constructor do the offsets
        // have to say which one it was, and several may cover them by accident.
        StructLineNumberTableAttribute owner = dynamicInitializerTable(className, methodKey);
        if (owner == null) {
          owner = initializerTable(className, mapping.keySet());
        }
        if (owner != null && gapAlign) {
          // The lifted initializer's offsets belong to a constructor, not to a method the tracer
          // names, so there is no code to read an opcode from; the walk keeps its old rules.
          addMethodConstraints(owner, mapping, lines, candidates, entryLines, null, null, tracers,
            null);
          continue;
        }
        Integer target = fieldInitLine(className, mapping.keySet());
        if (target == null) {
          continue;
        }
        for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
          int ours = entry.getValue() + 1;
          if (ours < 1 || ours > lines.length) {
            continue;
          }
          entryLines.add(ours);
          add(shifts, conflicted, ours, target - ours);
        }
        continue;
      }
      StructLineNumberTableAttribute table = lineTable(className, methodKey);
      if (table == null) {
        continue;
      }
      if (gapAlign) {
        StructClass cls = DecompilerContext.getStructContext().getClass(className);
        StructMethod method = cls == null ? null : cls.getMethod(methodKey);
        addMethodConstraints(table, mapping, lines, candidates, entryLines, cls, method, tracers,
          joinBlocked);
        continue;
      }
      for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
        int ours = entry.getValue() + 1; // one based line in this file
        int target = table.findLineNumber(entry.getKey());
        if (target < 0 || ours < 1 || ours > lines.length) {
          continue;
        }
        entryLines.add(ours);
        add(shifts, conflicted, ours, target - ours);
      }
    }
    // An implicit constructor has no source text to map, yet javac places its one entry on the
    // class declaration's line. Without this constraint the declaration never moves, and every
    // class with a default constructor stays shifted by however far the original header was.
    addImplicitConstructorConstraints(tracers, lines, shifts, conflicted, entryLines, root);
    resolveCandidates(candidates, shifts, conflicted, unmergeable, inherited, entryLines);

    for (int line : conflicted) {
      shifts.remove(line);
    }
    if (shifts.isEmpty()) {
      return text;
    }

    List<int[]> inserts = new ArrayList<>();
    List<Integer> removals = new ArrayList<>();
    List<Integer> joins = new ArrayList<>();
    if (gapAlign) {
      if (!walkGaps(lines, shifts, unmergeable, inherited, entryLines, joinBlocked, records, inserts,
          removals, joins)) {
        return text;
      }
    }
    else {
      int previous = 0;
      int previousIndex = -1;
      for (Map.Entry<Integer, Integer> entry : shifts.entrySet()) {
        int index = entry.getKey() - 1;
        int target = entry.getValue();
        if (index < 0 || index > lines.length) {
          return text;
        }
        if (target > previous) {
          if (insideTextBlock(lines, index)) {
            return text;
          }
          inserts.add(new int[]{index, target - previous});
        } else if (target < previous) {
          int want = previous - target;
          int need = want;
          int lowest = previousIndex;
          for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
            if (removable(lines, i)) {
              removals.add(i);
              need--;
            }
          }
          for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
            // A join moves line i onto line i-1, so neither may be a line another edit deletes.
            if (joinable(lines, i, entryLines, false)
                && joinRecordsSupport(i + 1, i, entry.getKey() + entry.getValue(), records)
                && !removals.contains(i) && !removals.contains(i - 1) && !joins.contains(i)) {
              joins.add(i);
              need--;
            }
          }
          target = previous - (want - need);
          if (debug && need > 0) {
            System.err.println("underpaid line " + entry.getKey() + " want " + want + " unpaid " + need
              + " from " + lowest + " to " + index);
          }
        }
        previous = target;
        previousIndex = index;
      }
    }
    if (debug) {
      System.err.println("align " + text.hashCode() + " shifts " + shifts.size()
        + " conflicts " + conflicted.size()
        + " inserts " + inserts.stream().map(a -> a[0] + "+" + a[1]).toList()
        + " removals " + removals.size() + " joins " + joins.size());
      String dump = System.getenv("NEUROFLOWER_LINEALIGN_DUMP");
      if (dump != null) {
        String[] range = dump.split(",");
        int from = range.length > 0 ? Integer.parseInt(range[0].trim()) : 205;
        int to = range.length > 1 ? Integer.parseInt(range[1].trim()) : from + 35;
        for (int i = Math.max(1, from); i <= Math.min(to, lines.length); i++) {
          System.err.println("L" + i + " shift=" + shifts.get(i) + " | " + lines[i - 1]);
        }
      }
    }
    if (inserts.isEmpty() && removals.isEmpty() && joins.isEmpty()) {
      return text;
    }

    List<int[]> edits = new ArrayList<>();
    for (int[] insert : inserts) {
      edits.add(new int[]{insert[0], 0, insert[1]});
    }
    for (int removal : removals) {
      edits.add(new int[]{removal, 1, 0});
    }
    for (int join : joins) {
      edits.add(new int[]{join, 2, 0});
    }
    edits.sort((a, b) -> Integer.compare(b[0], a[0]));
    List<String> edited = new ArrayList<>(List.of(lines));
    for (int[] edit : edits) {
      if (edit[1] == 0) {
        for (int k = 0; k < edit[2]; k++) {
          edited.add(edit[0], PADDING);
        }
      } else if (edit[1] == 1) {
        edited.remove(edit[0]);
      } else {
        edited.set(edit[0] - 1, edited.get(edit[0] - 1) + " " + edited.get(edit[0]).trim());
        edited.remove(edit[0]);
      }
    }
    String aligned = String.join(separator, edited);
    // Alignment may only move lines and whitespace. If the token text changed at all, the layout
    // was wrong: keep the unaligned text rather than ship a source that may not compile.
    if (!normalized(aligned, separator).equals(normalized(text, separator))) {
      return text;
    }
    return aligned;
  }

  /**
   * Puts a field initializer's first instruction on the declaration's line.
   *
   * <p>javac records a field's declaration at the position of the initializer expression, and the
   * first instruction the expression emits inherits that line. For an instance field that line is
   * the declaration block's first line, annotations included, while the printer writes the
   * annotation above the signature and records the instruction at the signature's position. The
   * printer records the declaration anchor under a {@code <field-decl field owner>} key; the
   * owner's table gives the line, and the argument's own position yields to it without losing the
   * printed position the constant-name pass reads.
   *
   * <p>The anchor is applied to two tracers. The owner's is the constructor the initializer was
   * lifted from, which carries the instruction's line table. The other is the initializer's own
   * tracer, keyed {@code <field-init field>}: it is what the aligner walks for a lifted
   * initializer, and leaving it on the signature's line would contradict the owner's entry.
   */
  private static void applyFieldDeclarationAnchors(
      Map<Pair<String, String>, BytecodeMappingTracer> tracers) {
    Map<Pair<String, String>, Map<Integer, Integer>> anchors = new java.util.HashMap<>();
    Map<Pair<String, String>, Map<Integer, Integer>> initializerAnchors = new java.util.HashMap<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      String methodKey = entry.getKey().b;
      if (!methodKey.startsWith("<field-decl ") || !methodKey.endsWith(">")) {
        continue;
      }
      String body = methodKey.substring("<field-decl ".length(), methodKey.length() - 1);
      // A field name holds no whitespace, so the first space ends it and the owner key -- which
      // may itself hold one -- follows.
      int space = body.indexOf(' ');
      String field = space < 0 ? null : body.substring(0, space);
      String owner = space < 0 ? body : body.substring(space + 1);
      anchors.computeIfAbsent(Pair.of(entry.getKey().a, owner), k -> new java.util.HashMap<>())
        .putAll(entry.getValue().getMapping());
      if (field != null && !field.isEmpty()) {
        initializerAnchors.computeIfAbsent(
          Pair.of(entry.getKey().a, "<field-init " + field + ">"), k -> new java.util.HashMap<>())
          .putAll(entry.getValue().getMapping());
      }
    }
    applyAnchors(tracers, anchors);
    applyAnchors(tracers, initializerAnchors);
  }

  /** Lowers the named tracers' entries to the declaration anchor where the anchor sits earlier. */
  private static void applyAnchors(Map<Pair<String, String>, BytecodeMappingTracer> tracers,
      Map<Pair<String, String>, Map<Integer, Integer>> anchors) {
    for (Map.Entry<Pair<String, String>, Map<Integer, Integer>> anchor : anchors.entrySet()) {
      BytecodeMappingTracer tracer = tracers.get(anchor.getKey());
      if (tracer == null) {
        continue;
      }
      for (Map.Entry<Integer, Integer> offset : anchor.getValue().entrySet()) {
        Integer current = tracer.getMapping().get(offset.getKey());
        if (current == null || offset.getValue() < current) {
          tracer.getMapping().put(offset.getKey(), offset.getValue());
        }
      }
    }
  }

  /**
   * Joins two printed lines that the original's table puts on the same source line.
   *
   * <p>Each line carries the bytecode offsets the printer wrote its statements from, and the
   * original's table gives each offset its source line. Two adjacent lines whose offsets all map to
   * one and the same line can only mean the original wrote those statements on one line; the join
   * is proven by the table rather than guessed from a missing entry. Only offsets of one method are
   * joined, so two lambdas that happen to share a target line stay apart.
   *
   * <p>A line whose offsets include no entry start of their own is not a source line of the
   * original: it inherits the line of the expression it continues, and joins it when the two
   * settle on the same line. A line opening with a binary operator or a closing bracket cannot
   * begin a statement, so a preceding line with no entry start of its own belongs to it.
   */
  private static String joinSameTargetLines(String text, String separator, String[] lines,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, LineRecords records) {
    Map<Integer, Integer> target = new java.util.HashMap<>();
    Map<Integer, String> owner = new java.util.HashMap<>();
    Set<Integer> mixed = new HashSet<>();
    Set<Integer> sharedOwner = new HashSet<>();
    Map<Integer, Set<Integer>> targets = new java.util.HashMap<>();
    Map<Integer, Set<Integer>> exact = new java.util.HashMap<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      String methodKey = tracerEntry.getKey().b;
      if (methodKey.startsWith("<field-init ")) {
        continue;
      }
      StructLineNumberTableAttribute table = lineTable(tracerEntry.getKey().a, methodKey);
      if (table == null) {
        continue;
      }
      int[] raw = table.getRawData();
      Set<Integer> own = new HashSet<>();
      for (int i = 0; i + 1 < raw.length; i += 2) {
        own.add(raw[i]);
      }
      for (Map.Entry<Integer, Integer> entry : tracerEntry.getValue().getMapping().entrySet()) {
        int line = entry.getValue() + 1;
        int source = table.findLineNumber(entry.getKey());
        if (source < 0 || line < 1 || line > lines.length) {
          continue;
        }
        Integer previous = target.putIfAbsent(line, source);
        if (previous != null && previous != source) {
          mixed.add(line);
        }
        String method = owner.putIfAbsent(line, methodKey);
        if (method != null && !method.equals(methodKey)) {
          sharedOwner.add(line);
          mixed.add(line);
        }
        targets.computeIfAbsent(line, k -> new java.util.TreeSet<>()).add(source);
        if (own.contains(entry.getKey())) {
          exact.computeIfAbsent(line, k -> new java.util.TreeSet<>()).add(source);
        }
      }
    }
    java.util.TreeSet<Integer> joins = new java.util.TreeSet<>();
    Map<Integer, Integer> joinAbove = new java.util.HashMap<>();
    java.util.TreeSet<Integer> removedLines = new java.util.TreeSet<>();
    for (int line = 2; line <= lines.length; line++) {
      if (owner.get(line) == null || sharedOwner.contains(line) || !mergeableWithEvidence(lines, line)) {
        continue;
      }
      // A blank line or a label standing alone is not a line of the original: the aligner deletes
      // it anyway. Looking through it lets a join the two texts prove still happen when the
      // printer put one between them; the skipped lines move onto the joined line with it.
      int aboveLine = line - 1;
      while (aboveLine >= 1 && owner.get(aboveLine) == null && skippablePad(lines[aboveLine - 1])
          && !insideTextBlock(lines, aboveLine - 1)) {
        aboveLine--;
      }
      if (aboveLine < 1 || owner.get(aboveLine) == null || sharedOwner.contains(aboveLine)) {
        continue;
      }
      Integer here = target.get(line);
      Integer above = target.get(aboveLine);
      // Two lines whose instructions the original's table puts on one and the same source line
      // belong together even when the printer wrote them from two methods: an inline lambda's body
      // starts on the line the enclosing expression continues, and both tables name that line.
      boolean same = here != null && above != null && here.equals(above)
        && !mixed.contains(line) && !mixed.contains(aboveLine);
      // A line the table gives no entry of its own is not a line of the original: every
      // instruction printed on it inherits a line of the expression above, so the printer broke
      // an expression the original kept on fewer lines. It belongs to the line above when the
      // two settle on the same line, and to this one when the line above has no entry at all.
      Integer resolved = resolvedTarget(line, targets, exact);
      Integer aboveResolved = resolvedTarget(aboveLine, targets, exact);
      boolean inheritsAbove = !exact.containsKey(line) && resolved != null
        && resolved.equals(aboveResolved);
      // The line above may belong to this one only when both hold instructions the table places
      // on the same source lines: the merge then moves no instruction onto a line it never had.
      // Two operands the table splits across lines keep their break.
      boolean absorbsAbove = !exact.containsKey(aboveLine) && aboveResolved == null
        && resolved != null && targets.containsKey(aboveLine)
        && targets.get(aboveLine).equals(targets.get(line))
        && continuesAbove(lines[line - 1]);
      Integer joinTargetValue = target.get(line);
      if ((same || inheritsAbove || absorbsAbove) && joinTargetValue != null
          && joinRecordsSupport(line, aboveLine, joinTargetValue, records)) {
        joins.add(line);
        joinAbove.put(line, aboveLine);
        for (int removed = line; removed > aboveLine; removed--) {
          removedLines.add(removed);
        }
      }
    }
    if (joins.isEmpty()) {
      return null;
    }
    List<String> edited = new ArrayList<>(List.of(lines));
    for (int line : joins.descendingSet()) {
      int aboveLine = joinAbove.get(line);
      StringBuilder merged = new StringBuilder(edited.get(aboveLine - 1));
      for (int joined = aboveLine + 1; joined <= line; joined++) {
        merged.append(' ').append(edited.get(joined - 1).trim());
      }
      edited.set(aboveLine - 1, merged.toString());
      for (int removed = line; removed > aboveLine; removed--) {
        edited.remove(removed - 1);
      }
    }
    for (BytecodeMappingTracer tracer : tracers.values()) {
      for (Map.Entry<Integer, Integer> entry : tracer.getMapping().entrySet()) {
        int line = entry.getValue() + 1;
        int removed = removedLines.headSet(line, true).size();
        entry.setValue(line - removed - 1);
      }
    }
    if (debug) {
      System.err.println("same-target joins " + joins.size());
    }
    return String.join(separator, edited);
  }

  /**
   * The source line a printed line settles on, by the same rule the shift walk uses: its own
   * entries first, else the one inherited line every offset agrees on.
   */
  private static Integer resolvedTarget(int line, Map<Integer, Set<Integer>> targets,
      Map<Integer, Set<Integer>> exact) {
    Set<Integer> own = exact.get(line);
    if (own != null) {
      return own.iterator().next();
    }
    Set<Integer> all = targets.get(line);
    return all != null && all.size() == 1 ? all.iterator().next() : null;
  }

  /** A line that cannot begin a statement: it opens with a binary operator or a closing bracket. */
  private static boolean continuesAbove(String line) {
    String trimmed = line.trim();
    return !trimmed.isEmpty() && "+-*/%&|^?:)".indexOf(trimmed.charAt(0)) >= 0;
  }

  /** The printed lines' records, grouped so a join can tell where its evidence came from. */
  private static final class LineRecords {
    final Map<Integer, Pair<String, String>> lineMethod;
    final Set<Integer> shared;
    final Map<Integer, int[]> lineSpan;
    final Map<Integer, Set<Integer>> lineOffsets;
    final Map<Pair<String, String>, Map<Integer, Integer>> methodMapping;
    final Map<Pair<String, String>, StructLineNumberTableAttribute> methodTables;
    final Map<Pair<String, String>, Set<Integer>> methodTargets;

    LineRecords(Map<Integer, Pair<String, String>> lineMethod, Set<Integer> shared,
        Map<Integer, int[]> lineSpan, Map<Integer, Set<Integer>> lineOffsets,
        Map<Pair<String, String>, Map<Integer, Integer>> methodMapping,
        Map<Pair<String, String>, StructLineNumberTableAttribute> methodTables,
        Map<Pair<String, String>, Set<Integer>> methodTargets) {
      this.lineMethod = lineMethod;
      this.shared = shared;
      this.lineSpan = lineSpan;
      this.lineOffsets = lineOffsets;
      this.methodMapping = methodMapping;
      this.methodTables = methodTables;
      this.methodTargets = methodTargets;
    }
  }

  /**
   * Groups every method record by the printed line it names.
   *
   * <p>A line usually belongs to one method, but an inline lambda's body shares the enclosing
   * method's text, so a line whose records come from two methods is marked shared and its records
   * are not used to prove a join.
   */
  private static LineRecords lineRecords(Map<Pair<String, String>, BytecodeMappingTracer> tracers,
      String[] lines) {
    Map<Integer, Pair<String, String>> lineMethod = new java.util.HashMap<>();
    Set<Integer> shared = new HashSet<>();
    Map<Integer, int[]> lineSpan = new java.util.HashMap<>();
    Map<Integer, Set<Integer>> lineOffsets = new java.util.HashMap<>();
    Map<Pair<String, String>, Map<Integer, Integer>> methodMapping = new java.util.HashMap<>();
    Map<Pair<String, String>, StructLineNumberTableAttribute> methodTables = new java.util.HashMap<>();
    Map<Pair<String, String>, Set<Integer>> methodTargets = new java.util.HashMap<>();
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> tracerEntry : tracers.entrySet()) {
      Pair<String, String> method = tracerEntry.getKey();
      String methodKey = method.b;
      if (methodKey.startsWith("<field-init ") || methodKey.startsWith("<field-decl ")) {
        continue;
      }
      StructLineNumberTableAttribute table = lineTable(method.a, methodKey);
      if (table == null) {
        continue;
      }
      Map<Integer, Integer> mapping = tracerEntry.getValue().getMapping();
      methodMapping.put(method, mapping);
      methodTables.put(method, table);
      Set<Integer> targets = methodTargets.computeIfAbsent(method, k -> new HashSet<>());
      for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
        int target = table.findLineNumber(entry.getKey());
        if (target >= 0) {
          targets.add(target);
        }
        int line = entry.getValue() + 1;
        if (line < 1 || line > lines.length) {
          continue;
        }
        Pair<String, String> owner = lineMethod.putIfAbsent(line, method);
        if (owner != null && !owner.equals(method)) {
          shared.add(line);
        }
        lineOffsets.computeIfAbsent(line, k -> new HashSet<>()).add(entry.getKey());
        int[] span = lineSpan.get(line);
        if (span == null) {
          lineSpan.put(line, new int[]{entry.getKey(), entry.getKey()});
        }
        else {
          span[0] = Math.min(span[0], entry.getKey());
          span[1] = Math.max(span[1], entry.getKey());
        }
      }
    }
    return new LineRecords(lineMethod, shared, lineSpan, lineOffsets, methodMapping, methodTables,
      methodTargets);
  }

  /**
   * Whether the class file's records let a join of {@code lower} onto {@code upper} stand.
   *
   * <p>An instruction has one source position, so a byte of it recorded beside one printed line
   * while another byte sits on a different line is a printer artifact -- the store ending a catch
   * body's expression is recorded beside the catch header. The upper line's record then proves
   * nothing about where its text sits, and the equal target it seemed to show is no evidence.
   *
   * <p>An entry start the printer never mapped marks a source line that no printed instruction
   * holds: the synthetic store javac places on the closing brace of a synchronized block, or on
   * the brace that ends a switch expression. When that line is exactly the next one after the line
   * the join would settle on, the brace's text belongs there and the join would erase the line --
   * the walk then leaves the gap underpaid, and the brace lands on its own line.
   */
  private static boolean joinRecordsSupport(int lower, int upper, int joinTarget, LineRecords records) {
    if (records.shared.contains(lower) || records.shared.contains(upper)) {
      return true;
    }
    Pair<String, String> lowerMethod = records.lineMethod.get(lower);
    Pair<String, String> upperMethod = records.lineMethod.get(upper);
    if (lowerMethod != null && upperMethod != null && !lowerMethod.equals(upperMethod)) {
      return true;
    }
    Pair<String, String> method = lowerMethod != null ? lowerMethod : upperMethod;
    if (method == null) {
      return true;
    }
    int[] lowerSpan = records.lineSpan.get(lower);
    int[] upperSpan = records.lineSpan.get(upper);
    if (isSplitRecord(method, upper, records)) {
      // One instruction's bytes recorded on two printed lines: the printer wrote an operand of a
      // later statement beside the text above it. The upper line's record is stale and proves
      // nothing about where that text sits.
      return false;
    }
    int max = Math.max(lowerSpan == null ? -1 : lowerSpan[1], upperSpan == null ? -1 : upperSpan[1]);
    if (max < 0) {
      return true;
    }
    StructLineNumberTableAttribute table = records.methodTables.get(method);
    Map<Integer, Integer> mapping = records.methodMapping.get(method);
    if (table == null || mapping == null) {
      return true;
    }
    int[] raw = table.getRawData();
    int next = Integer.MAX_VALUE;
    for (int i = 0; i + 1 < raw.length; i += 2) {
      if (raw[i] > max && raw[i] < next) {
        next = raw[i];
      }
    }
    if (next == Integer.MAX_VALUE || mapping.containsKey(next)) {
      return true;
    }
    int target = table.findLineNumber(next);
    Set<Integer> printed = records.methodTargets.get(method);
    return target != joinTarget + 1 || printed != null && printed.contains(target);
  }

  /** A line the aligner deletes on its own: blank padding, or a label standing alone. */
  private static boolean skippablePad(String line) {
    String trimmed = line.trim();
    if (trimmed.isEmpty() || trimmed.equals(PADDING)) {
      return true;
    }
    // `label36:` — an identifier and its colon, with no statement after it on the line.
    int colon = trimmed.indexOf(':');
    if (colon <= 0 || colon != trimmed.length() - 1) {
      return false;
    }
    for (int i = 0; i < colon; i++) {
      char c = trimmed.charAt(i);
      if (i == 0 ? !Character.isJavaIdentifierStart(c) : !Character.isJavaIdentifierPart(c)) {
        return false;
      }
    }
    return true;
  }

  /** A line that may be joined onto the one above: no comment, no blank, not in a text block. */
  private static boolean mergeableWithEvidence(String[] lines, int lineNumber) {
    int index = lineNumber - 1;
    if (index <= 0 || index >= lines.length) {
      return false;
    }
    if (insideTextBlock(lines, index) || insideTextBlock(lines, index - 1)) {
      return false;
    }
    if (lines[index - 1].contains("//") || lines[index - 1].contains("/*") || lines[index].contains("*/")) {
      return false;
    }
    return !lines[index].trim().isEmpty();
  }

  private static String normalized(String text, String separator) {
    StringBuilder builder = new StringBuilder(text.length());
    for (String line : text.split(java.util.regex.Pattern.quote(separator), -1)) {
      String trimmed = line.trim();
      if (trimmed.equals(PADDING)) {
        continue;
      }
      for (int i = 0; i < line.length(); i++) {
        char c = line.charAt(i);
        if (!Character.isWhitespace(c)) {
          builder.append(c);
        }
      }
    }
    return builder.toString();
  }

  /**
   * The line table of the constructor a lifted field initializer's offsets were recorded from.
   *
   * <p>Every constructor's offsets start at zero, so the byte ranges alone cannot name the owner:
   * a small delegating constructor can cover the initializer's offsets by accident. The printer
   * lifted the initializer expression out of the first constructor that reaches it, and the
   * decompiler kept that constructor on the wrapper; its table is the one that places the
   * declarations, whichever other constructors share the offsets.
   */
  private static StructLineNumberTableAttribute dynamicInitializerTable(String className,
      String methodKey) {
    if (!methodKey.startsWith("<field-init ") || !methodKey.endsWith(">")) {
      return null;
    }
    String field = methodKey.substring("<field-init ".length(), methodKey.length() - 1);
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    boolean known = false;
    if (cls != null) {
      for (StructField fd : cls.getFields()) {
        if (fd.getName().equals(field)) {
          known = true;
          break;
        }
      }
    }
    if (!known) {
      // The key exists for every instance field, initializer or not; a name the class does not
      // declare carries no initializer whose offsets a constructor's table could describe.
      return null;
    }
    ClassesProcessor.ClassNode node =
      DecompilerContext.getClassProcessor().getMapRootClasses().get(className);
    if (node == null) {
      return null;
    }
    // The class being written has already had its wrapper destroyed, so the owner it was given
    // survives on the node; a nested class's wrapper is still alive when its file is written.
    StructMethod owner = node.dynamicInitializerOwner;
    if (owner == null) {
      ClassWrapper wrapper = node.getWrapper();
      owner = wrapper == null ? null : wrapper.getDynamicInitializerOwner();
    }
    return owner == null ? null
      : owner.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
  }

  /**
   * The line table of the constructor a lifted field initializer was generated into, or null when
   * several constructors contain its offsets or none does. The printer records the initializer
   * once, at its declaration, while javac emitted it into every constructor that reaches it; the
   * copy whose code covers every recorded offset is the one whose table places the declarations.
   */
  private static StructLineNumberTableAttribute initializerTable(String className,
      java.util.Set<Integer> offsets) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null || offsets.isEmpty()) {
      return null;
    }
    StructLineNumberTableAttribute found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!"<init>".equals(method.getName())) {
        continue;
      }
      if (method.getInstructionSequence() == null) {
        try {
          method.expandData(cls);
        }
        catch (Exception e) {
          continue;
        }
      }
      FullInstructionSequence code = method.getInstructionSequence();
      if (code == null || !coversOffsets(code, offsets)) {
        continue;
      }
      if (found != null) {
        return null;
      }
      found = method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    }
    return found;
  }

  private static boolean coversOffsets(
      FullInstructionSequence code, java.util.Set<Integer> offsets) {
    java.util.Set<Integer> remaining = new HashSet<>(offsets);
    for (Instruction instruction : code) {
      // The tracer records operand bytes as well as instruction starts, so an offset is inside
      // the method when any instruction covers it.
      for (int offset = instruction.startOffset; offset < instruction.startOffset + instruction.length; offset++) {
        remaining.remove(offset);
      }
      if (remaining.isEmpty()) {
        return true;
      }
    }
    return remaining.isEmpty();
  }

  /**
   * The original source line of an instance field initializer. Its offsets belong to one of the
   * constructors, and in that constructor the whole initializer maps to the field's line; other
   * constructors map those offsets to unrelated lines, so the line every offset agrees on is the
   * field's.
   */
  private static Integer fieldInitLine(String className, java.util.Set<Integer> offsets) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null) {
      return null;
    }
    Integer found = null;
    for (StructMethod method : cls.getMethods()) {
      if (!"<init>".equals(method.getName())) {
        continue;
      }
      StructLineNumberTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (table == null) {
        continue;
      }
      Set<Integer> distinct = new HashSet<>();
      for (int offset : offsets) {
        int line = table.findLineNumber(offset);
        if (line >= 0) {
          distinct.add(line);
        }
      }
      if (distinct.size() == 1) {
        int line = distinct.iterator().next();
        if (found != null && found != line) {
          return null;
        }
        found = line;
      }
    }
    return found;
  }

  private static void addImplicitConstructorConstraints(
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines,
      ClassesProcessor.ClassNode root) {
    if (root != null) {
      anchorClassLines(root, 0, tracers, lines, shifts, conflicted, entryLines);
    }
  }

  private static void anchorClassLines(ClassesProcessor.ClassNode node, int enclosingLine,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines) {
    String className = node.classStruct == null ? null : node.classStruct.qualifiedName;
    int declaration = -1;
    if (className != null) {
      String simple = className.substring(className.lastIndexOf('/') + 1);
      int dollar = simple.lastIndexOf('$');
      if (dollar >= 0) {
        simple = simple.substring(dollar + 1);
      }
      if (!simple.isEmpty() && !Character.isJavaIdentifierStart(simple.charAt(0))
          && node.simpleName != null) {
        // A local class's binary name numbers it -- FillCommand$1UpdatedPosition -- while the
        // source, and the InnerClasses entry, call it UpdatedPosition.
        simple = node.simpleName;
      }
      if (!simple.isEmpty() && Character.isJavaIdentifierStart(simple.charAt(0))) {
        declaration = classDeclarationLine(lines, simple, enclosingLine,
          firstMemberLine(className, tracers, lines), declarationHint(node.classStruct, className, tracers));
        if (declaration >= 0) {
          anchorOne(node.classStruct, className, declaration, tracers, lines, shifts, conflicted, entryLines);
        }
      }
    }
    int childEnclosing = declaration >= 0 ? declaration : enclosingLine;
    for (ClassesProcessor.ClassNode nested : node.nested) {
      anchorClassLines(nested, childEnclosing, tracers, lines, shifts, conflicted, entryLines);
    }
  }

  private static int firstMemberLine(String className,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines) {
    int first = lines.length + 1;
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      if (!className.equals(entry.getKey().a)) {
        continue;
      }
      for (int line : entry.getValue().getMapping().values()) {
        first = Math.min(first, line + 1);
      }
    }
    return first;
  }

  private static void anchorOne(StructClass cls, String className, int declaration,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> entryLines) {
    {
      // A record's generated members (hashCode, equals, toString, accessors) are all attributed to
      // the first line of the record declaration -- annotations included, which no printed
      // construct maps; the keyword alone would leave the annotation behind and move only half
      // the declaration.
      if (cls.getRecordComponents() != null) {
        int top = classDeclarationTop(lines, declaration, 0);
        int target = -1;
        for (String[] generated : RECORD_MEMBERS) {
          target = generatedTarget(cls, className, tracers, generated[0], generated[1]);
          if (target >= 0) {
            break;
          }
        }
        if (target < 0) {
          for (StructRecordComponent component : cls.getRecordComponents()) {
            target = generatedTarget(cls, className, tracers,
              component.getName(), "()" + component.getDescriptor());
            if (target >= 0) {
              break;
            }
          }
        }
        if (target >= 0) {
          entryLines.add(top);
          add(shifts, conflicted, top, target - top);
        }
      }
      // An enum's values() and $values() are anchored to the enum declaration line, which no
      // printed construct maps; without it the declaration drifts by however many header lines the
      // original had.
      if ((cls.getAccessFlags()
          & org.jetbrains.java.decompiler.code.CodeConstants.ACC_ENUM) != 0) {
        StructMethod values = cls.getMethod("values", "()[L" + className + ";");
        StructLineNumberTableAttribute table = values == null ? null
          : values.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        int target = table == null ? -1 : table.findLineNumber(0);
        if (target >= 0) {
          // The target's entry names the first line of the declaration block, annotations
          // included; javac starts the enum there. Anchoring the keyword alone would leave the
          // annotation above on its old line and move only the enum.
          int top = classDeclarationTop(lines, declaration, 0);
          entryLines.add(top);
          add(shifts, conflicted, top, target - top);
        }
      }
      // A class that uses assertions carries a synthetic $assertionsDisabled field, and javac
      // writes the <clinit> that fills it with one line entry, the class declaration's. The source
      // wrote no static initializer block, so no printed construct maps that line. The prelude is
      // the first instruction; when nothing printed claims it, its line is the class header's,
      // whether or not other initializers follow in the same table.
      if (hasAssertionsDisabled(cls)) {
        StructMethod clinit = cls.getMethod(org.jetbrains.java.decompiler.code.CodeConstants.CLINIT_NAME, "()V");
        BytecodeMappingTracer tracer = clinit == null ? null : tracers.get(
          Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
            clinit.getName(), clinit.getDescriptor())));
        StructLineNumberTableAttribute table = clinit == null ? null
          : clinit.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        if ((tracer == null || !tracer.getMapping().containsKey(0)) && table != null) {
          int target = table.findLineNumber(0);
          if (target >= 0) {
            int top = classDeclarationTop(lines, declaration, 0);
            entryLines.add(top);
            add(shifts, conflicted, top, target - top);
          }
        }
      }
      for (StructMethod method : cls.getMethods()) {
        boolean bridge = (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_BRIDGE) != 0;
        boolean accessor = isSyntheticAccessor(method);
        if (!"<init>".equals(method.getName()) && !bridge && !accessor) {
          continue;
        }
        BytecodeMappingTracer tracer = tracers.get(
          Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
            method.getName(), method.getDescriptor())));
        if (tracer != null && !tracer.getMapping().isEmpty()) {
          continue; // an explicit member carries its own constraints
        }
        StructLineNumberTableAttribute table =
          method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        if (table == null) {
          continue;
        }
        int target = table.findLineNumber(0);
        if (target < 0) {
          continue;
        }
        if ((bridge || accessor) && !singleLine(table)) {
          continue; // a bridge spanning several lines is not anchored to the declaration
        }
        int anchor = bridge || accessor
          ? classDeclarationTop(lines, declaration, 0)
          : declaration;
        entryLines.add(anchor);
        add(shifts, conflicted, anchor, target - anchor);
      }
    }
  }

  /** Whether javac generated the class's synthetic {@code $assertionsDisabled} field. */
  private static boolean hasAssertionsDisabled(StructClass cls) {
    for (StructField field : cls.getFields()) {
      if ("$assertionsDisabled".equals(field.getName())
          && (field.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_SYNTHETIC) != 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * The line a record's generated member is attributed to, or minus one when the source wrote
   * that member itself. A generated member is not printed, so its single entry names the record
   * declaration's first line; an explicit one carries its own constraints and is left alone.
   */
  private static int generatedTarget(StructClass cls, String className,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String name, String descriptor) {
    String key = org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(name, descriptor);
    if (tracers.containsKey(Pair.of(className, key))) {
      return -1;
    }
    StructMethod method = cls.getMethod(name, descriptor);
    StructLineNumberTableAttribute table = method == null ? null
      : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
    return table == null ? -1 : table.findLineNumber(0);
  }

  /**
   * A compiler-generated access method for a private member read from a nested class.
   *
   * <p>It is not printed, and javac gives its single line entry the class declaration's line, so
   * it anchors the declaration exactly like a bridge.
   */
  private static boolean isSyntheticAccessor(StructMethod method) {
    return method.getName().startsWith("access$")
      && (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_SYNTHETIC) != 0;
  }

  private static void collectNodes(ClassesProcessor.ClassNode node, List<ClassesProcessor.ClassNode> out) {
    if (node == null) {
      return;
    }
    out.add(node);
    for (ClassesProcessor.ClassNode nested : node.nested) {
      collectNodes(nested, out);
    }
  }

  private static boolean singleLine(StructLineNumberTableAttribute table) {
    int[] raw = table.getRawData();
    int first = raw.length < 2 ? -1 : raw[1];
    for (int i = 3; i < raw.length; i += 2) {
      if (raw[i] != first) {
        return false;
      }
    }
    return first >= 0;
  }

  /**
   * The line of this class's declaration in the printed file.
   *
   * <p>Several nested classes may share a simple name, so a file can hold more than one matching
   * declaration. The last one before the class's first member used to be taken, which fails for a
   * class with no members at all: the search then covers the rest of the file and lands on a
   * sibling's declaration. The target's own line for the class's anchor -- its hidden constructor,
   * its generated record members, or its enum's values() -- is where the declaration was, so the
   * candidate closest to it is the right one whenever such a line exists.
   */
  private static int classDeclarationLine(String[] lines, String simple, int enclosing, int beforeMember,
      int hint) {
    java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
      "\\b(?:class|record|enum|interface)\\s+" + java.util.regex.Pattern.quote(simple) + "\\b");
    int found = -1;
    int end = Math.min(lines.length, beforeMember - 1);
    int closest = Integer.MAX_VALUE;
    for (int i = Math.max(0, enclosing); i < end; i++) {
      if (!pattern.matcher(lines[i]).find()) {
        continue;
      }
      if (hint >= 0) {
        int distance = Math.abs((i + 1) - hint);
        if (distance < closest) {
          closest = distance;
          found = i + 1;
        }
      }
      else {
        found = i + 1;
      }
    }
    return found;
  }

  /** The line the target attributes this class's declaration to, or minus one when it says nothing. */
  private static int declarationHint(StructClass cls, String className,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers) {
    if (cls == null) {
      return -1;
    }
    if (cls.getRecordComponents() != null) {
      for (String[] generated : RECORD_MEMBERS) {
        String key = org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
          generated[0], generated[1]);
        if (tracers.containsKey(Pair.of(className, key))) {
          continue;
        }
        StructMethod method = cls.getMethod(generated[0], generated[1]);
        StructLineNumberTableAttribute table = method == null ? null
          : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
        int target = table == null ? -1 : table.findLineNumber(0);
        if (target >= 0) {
          return target;
        }
      }
    }
    if ((cls.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_ENUM) != 0) {
      StructMethod values = cls.getMethod("values", "()[L" + className + ";");
      StructLineNumberTableAttribute table = values == null ? null
        : values.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      int target = table == null ? -1 : table.findLineNumber(0);
      if (target >= 0) {
        return target;
      }
    }
    for (StructMethod method : cls.getMethods()) {
      boolean bridge = (method.getAccessFlags() & org.jetbrains.java.decompiler.code.CodeConstants.ACC_BRIDGE) != 0;
      boolean accessor = isSyntheticAccessor(method);
      if (!"<init>".equals(method.getName()) && !bridge && !accessor) {
        continue;
      }
      BytecodeMappingTracer tracer = tracers.get(
        Pair.of(className, org.jetbrains.java.decompiler.util.InterpreterUtil.makeUniqueKey(
          method.getName(), method.getDescriptor())));
      if (tracer != null && !tracer.getMapping().isEmpty()) {
        continue;
      }
      StructLineNumberTableAttribute table =
        method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (table == null) {
        continue;
      }
      int target = table.findLineNumber(0);
      if (target >= 0) {
        return target;
      }
    }
    return -1;
  }

  /** The first line of the declaration block, annotations and modifiers included; javac anchors bridges there. */
  private static int classDeclarationTop(String[] lines, int declaration, int enclosing) {
    if (declaration < 0) {
      return -1;
    }
    int top = declaration;
    for (int i = declaration - 2; i >= enclosing; i--) {
      String text = lines[i].trim();
      if (text.isEmpty() || text.equals(PADDING)) {
        continue;
      }
      if (annotationOnly(text) || modifiersOnly(text)) {
        top = i + 1;
        continue;
      }
      break;
    }
    return top;
  }

  /**
   * Whether the line holds nothing but declaration modifiers. A nested enum whose keyword was on
   * the line below its modifiers prints a redundant {@code static} alone: the target's values()
   * line is the modifier's, and the declaration block begins there.
   */
  private static boolean modifiersOnly(String text) {
    if (text.isEmpty()) {
      return false;
    }
    for (String word : text.split("\\s+")) {
      if (!DECLARATION_MODIFIERS.contains(word)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Whether the line holds nothing but annotations.
   *
   * <p>A member carrying an annotation on the same line as its signature -- {@code @Nullable
   * PlayerChatMessage getArgument(String name);} -- is the preceding member, not part of the
   * declaration below it. Only a line that ends after its annotation(s) belongs to the block.
   */
  private static boolean annotationOnly(String text) {
    int i = 0;
    while (true) {
      while (i < text.length() && Character.isWhitespace(text.charAt(i))) {
        i++;
      }
      if (i >= text.length() || text.charAt(i) != '@') {
        break;
      }
      i++;
      while (i < text.length() && (Character.isJavaIdentifierPart(text.charAt(i)) || text.charAt(i) == '.')) {
        i++;
      }
      while (i < text.length() && Character.isWhitespace(text.charAt(i))) {
        i++;
      }
      if (i < text.length() && text.charAt(i) == '(') {
        int depth = 0;
        while (i < text.length()) {
          char c = text.charAt(i++);
          if (c == '(') {
            depth++;
          }
          else if (c == ')') {
            depth--;
            if (depth == 0) {
              break;
            }
          }
          else if (c == '"') {
            while (i < text.length() && text.charAt(i) != '"') {
              if (text.charAt(i) == '\\') {
                i++;
              }
              i++;
            }
            i++;
          }
        }
      }
    }
    return i >= text.length();
  }

  private static StructLineNumberTableAttribute lineTable(String className, String methodKey) {
    StructClass cls = DecompilerContext.getStructContext().getClass(className);
    if (cls == null) {
      return null;
    }
    StructMethod method = cls.getMethod(methodKey);
    return method == null ? null : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
  }

  private static void add(TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, int line, int shift) {
    if (conflicted.contains(line)) {
      return;
    }
    Integer known = shifts.putIfAbsent(line, shift);
    if (known != null && known != shift) {
      shifts.remove(line);
      conflicted.add(line);
    }
  }

  /**
   * Builds the anchors one method at a time, in bytecode order.
   *
   * <p>An instruction can be recorded on a line earlier than the entry before it only when the
   * printer mapped it at a statement boundary rather than where its text sits: a lifted
   * initializer maps its last instruction to the declaration's line, and the store a switch
   * merges out of its arms maps to the header's. The instruction's text is then on the line the
   * previous entry closes, and the original's line continues that entry's by at most one. Such
   * a record moves its target there. A target that moves back belongs to an invocation printed
   * before its own arguments, and one that jumps ahead belongs to a synthetic closing-brace
   * mapping; both keep their own line, as any other entry does.
   */
  private static void addMethodConstraints(StructLineNumberTableAttribute table,
      Map<Integer, Integer> mapping, String[] lines, Map<Integer, List<int[]>> candidates,
      Set<Integer> entryLines, StructClass cls, StructMethod method,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, Set<Integer> joinBlocked) {
    int[] raw = table.getRawData();
    Set<Integer> exact = new HashSet<>();
    for (int i = 0; i + 1 < raw.length; i += 2) {
      exact.add(raw[i]);
    }
    List<int[]> entries = new ArrayList<>(mapping.size());
    for (Map.Entry<Integer, Integer> entry : mapping.entrySet()) {
      int ours = entry.getValue() + 1; // one based line in this file
      int target = table.findLineNumber(entry.getKey());
      if (target < 0 || ours < 1 || ours > lines.length) {
        continue;
      }
      int kind = 0;
      if (exact.contains(entry.getKey())) {
        kind = 1;
        Instruction instruction = cls == null || method == null ? null
          : instructionAt(method, cls, entry.getKey());
        if (instruction != null && instruction.opcode >= CodeConstants.opc_istore
            && instruction.opcode <= CodeConstants.opc_astore_3) {
          // A store ending a switch expression is placed on the closing brace's line while the
          // printer records it beside the last arm; the arm still starts where its own text does.
          kind = 2;
        }
      }
      entries.add(new int[]{entry.getKey(), ours, target, kind});
    }
    entries.sort((a, b) -> Integer.compare(a[0], b[0]));
    if (joinBlocked != null && cls != null && method != null) {
      // A loop's back-edge is emitted at the closing brace but the printer records it beside the
      // statement below, so its line's first record names the brace line above. When the anchor
      // is a statement -- a break after the loop -- paying its gap by joining would move that
      // statement onto the brace's line and erase the source line the branch proves; leaving the
      // gap underpaid keeps both lines. A brace line's own joins only gather closing braces, which
      // the table can share on one line, so it stays joinable.
      Set<Integer> firstLines = new HashSet<>();
      for (int[] entry : entries) {
        if (firstLines.add(entry[1]) && isBackwardGoto(instructionAt(method, cls, entry[0]))
            && entry[1] >= 1 && entry[1] <= lines.length
            && !lines[entry[1] - 1].trim().startsWith("}")) {
          joinBlocked.add(entry[1]);
        }
      }
    }
    int previousLine = -1;
    int highest = -1;
    Set<Integer> exactPrinted = new HashSet<>();
    for (int[] entry : entries) {
      // A switch's dispatch record carries no line of its own: the table places the comparison on
      // the switch's line while the printer writes it beside the label it matches, so the label's
      // printed line must never become an anchor. The text tells the two lines apart.
      String text = entry[1] >= 1 && entry[1] <= lines.length ? lines[entry[1] - 1].trim() : "";
      boolean label = text.startsWith("case ") || text.startsWith("default");
      boolean boundary = entry[1] < previousLine || entry[3] == 0 && entry[2] == highest && label;
      if (boundary && entry[2] >= highest && entry[2] <= highest + 1) {
        if (invocationKeepsItsLine(cls, method, tracers, lines, exactPrinted, entry, previousLine,
            highest)) {
          // The text on this record's own line opens the call, and the line it moved back from
          // carries the rest of the argument list; folding it there would lose the call's line.
          previousLine = entry[1];
          highest = Math.max(highest, entry[2]);
          entryLines.add(entry[1]);
          candidate(candidates, entry[1], entry[2] - entry[1], entry[3], entry[0]);
          if (entry[3] != 0) {
            exactPrinted.add(entry[1]);
          }
          continue;
        }
        highest = entry[2];
        entryLines.add(previousLine);
        candidate(candidates, previousLine, entry[2] - previousLine, entry[3], entry[0]);
        if (entry[3] != 0) {
          exactPrinted.add(previousLine);
        }
        continue;
      }
      previousLine = entry[1];
      highest = Math.max(highest, entry[2]);
      entryLines.add(entry[1]);
      candidate(candidates, entry[1], entry[2] - entry[1], entry[3], entry[0]);
      if (entry[3] != 0) {
        exactPrinted.add(entry[1]);
      }
    }
  }

  /**
   * Whether an invocation printed on an earlier line than the entry before it must stay there.
   *
   * <p>The printer writes a chained call before its arguments: the receiver and the first
   * arguments end the chain's line, while the rest of the argument list -- a block lambda's body
   * and its closing brace among them -- is printed on the lines below. The body is compiled into
   * a method of its own, and javac places its terminal return on the closing brace's line, so the
   * continuation is a source line in its own right that must not be folded into the call's.
   * When the invocation's own table line is the next source line after the chain, it anchors its
   * own printed line, and the lambda's return anchors the continuation; the call keeps its line.
   *
   * <p>Only facts read from the class file or the printed text qualify: the instruction is an
   * invocation; the printed line opens a chained call; the line the record moved back from
   * carries only arguments and a closing paren; no entry of this method's own is printed there;
   * and a block lambda of this method closes on that line, at a source line after the call's.
   */
  private static boolean invocationKeepsItsLine(StructClass cls, StructMethod method,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String[] lines,
      Set<Integer> exactPrinted, int[] entry, int previousLine, int highest) {
    if (cls == null || method == null || entry[3] == 0 || entry[1] >= previousLine) {
      return false;
    }
    if (entry[2] <= highest || entry[2] > highest + 1) {
      return false;
    }
    Instruction instruction = instructionAt(method, cls, entry[0]);
    if (instruction == null || !isInvoke(instruction.opcode)) {
      return false;
    }
    if (!opensCall(printedText(lines, entry[1])) || !carriesArgumentsOnly(printedText(lines, previousLine))) {
      return false;
    }
    if (exactPrinted.contains(previousLine)) {
      return false;
    }
    return closesLambda(cls, tracers, method.getName(), previousLine, entry[2]);
  }

  private static String printedText(String[] lines, int line) {
    return line >= 1 && line <= lines.length ? lines[line - 1].trim() : "";
  }

  private static boolean isInvoke(int opcode) {
    return opcode == CodeConstants.opc_invokevirtual || opcode == CodeConstants.opc_invokespecial
      || opcode == CodeConstants.opc_invokestatic || opcode == CodeConstants.opc_invokeinterface
      || opcode == CodeConstants.opc_invokedynamic;
  }

  /** A printed line that opens a chained call, such as {@code .thenAcceptAsync(value -> ...}. */
  private static boolean opensCall(String text) {
    if (text.isEmpty() || text.charAt(0) != '.') {
      return false;
    }
    int i = 1;
    while (i < text.length() && Character.isJavaIdentifierPart(text.charAt(i))) {
      i++;
    }
    return i > 1 && i < text.length() && text.charAt(i) == '(';
  }

  /** A printed line that carries only an invocation's remaining arguments and closing paren. */
  private static boolean carriesArgumentsOnly(String text) {
    if (text.isEmpty() || text.charAt(0) != '}' || text.charAt(text.length() - 1) != ')') {
      return false;
    }
    return text.indexOf(';') < 0 && text.indexOf('{') < 0;
  }

  /**
   * Whether a block lambda of this method closes on the printed line the invocation moved back
   * from, at a source line the table places after the invocation's own.
   *
   * <p>javac puts the lambda's terminal return on the line of its closing brace, and the printer
   * prints that return on the brace line too. When the return carries a line entry of its own --
   * the entry the table ends with, and the instruction an ordinary {@code return} -- that line is
   * the continuation's target, and the continuation needs no folding to stay on it.
   */
  private static boolean closesLambda(StructClass cls,
      Map<Pair<String, String>, BytecodeMappingTracer> tracers, String owner, int line,
      int callTarget) {
    String prefix = "lambda$" + owner + "$";
    for (Map.Entry<Pair<String, String>, BytecodeMappingTracer> entry : tracers.entrySet()) {
      if (!cls.qualifiedName.equals(entry.getKey().a) || !entry.getKey().b.startsWith(prefix)) {
        continue;
      }
      StructMethod method = cls.getMethod(entry.getKey().b);
      StructLineNumberTableAttribute table = method == null ? null
        : method.getAttribute(StructGeneralAttribute.ATTRIBUTE_LINE_NUMBER_TABLE);
      if (table == null) {
        continue;
      }
      int[] raw = table.getRawData();
      if (raw.length < 2) {
        continue;
      }
      int offset = raw[raw.length - 2];
      Instruction instruction = instructionAt(method, cls, offset);
      if (instruction == null || instruction.opcode != CodeConstants.opc_return) {
        continue;
      }
      Integer printed = entry.getValue().getMapping().get(offset);
      if (printed == null || printed + 1 != line) {
        continue;
      }
      if (table.findLineNumber(offset) > callTarget) {
        return true;
      }
    }
    return false;
  }

  /**
   * The inherited shift of a printed line that starts on an earlier line and holds one entry of
   * its own at its end, or null when the line has another shape.
   *
   * <p>A switch expression's value is stored by an instruction javac places on the line its closing
   * brace sits on, while the printer records the store beside the last arm it printed. The arm's
   * own instructions inherit the arm's line while the store's entry names the following source
   * line, so the printed line begins where its inherited instructions do, and the brace line that
   * follows it -- carrying no record of its own -- takes the store's line. Choosing the store's
   * shift instead would pull the arm one line down and force a join onto a statement, losing that
   * source line. The shape is proven only when every inherited instruction before the entry agrees
   * on the line above it and every one after it agrees with the entry.
   */
  private static Integer inheritedStartShift(List<int[]> candidates, int[] firstExact) {
    if (firstExact == null || firstExact[1] != 2) {
      return null;
    }
    Integer before = null;
    for (int[] candidate : candidates) {
      if (candidate == firstExact || candidate[1] != 0) {
        continue;
      }
      if (candidate[2] < firstExact[2]) {
        if (before != null && before != candidate[0]) {
          return null;
        }
        before = candidate[0];
      }
      else if (candidate[0] != firstExact[0]) {
        return null;
      }
    }
    return before != null && before == firstExact[0] - 1 ? before : null;
  }

  /** Whether the instruction is a goto that jumps backwards, such as a loop's back-edge. */
  private static boolean isBackwardGoto(Instruction instruction) {
    if (instruction == null
        || instruction.opcode != CodeConstants.opc_goto && instruction.opcode != CodeConstants.opc_goto_w) {
      return false;
    }
    return instruction.operand(0) < 0;
  }

  /**
   * Whether a printed line holds a store's record whose other bytes are recorded on another line.
   *
   * <p>One instruction has one source position, so a store split across two printed lines is a
   * printer artifact: the store that ends a catch body's expression is recorded beside the catch
   * header, while the rest of its statement is printed below. The line above then names a source
   * line its text does not occupy, and it cannot prove that the text below shared that line. The
   * shape is specific to stores: a local declaration's `new` is recorded on the declaration's
   * line while its operands are printed with the statement below, and joining the statement onto
   * its declaration is harmless because the declaration line carries no instruction at all.
   */
  private static boolean isSplitRecord(Pair<String, String> method, int line, LineRecords records) {
    Set<Integer> offsets = records.lineOffsets.get(line);
    if (offsets == null) {
      return false;
    }
    StructClass cls = DecompilerContext.getStructContext().getClass(method.a);
    StructMethod struct = cls == null ? null : cls.getMethod(method.b);
    Map<Integer, Integer> mapping = records.methodMapping.get(method);
    if (struct == null || mapping == null) {
      return false;
    }
    for (int offset : offsets) {
      Instruction instruction = instructionAt(struct, cls, offset);
      if (instruction == null || instruction.length <= 1
          || instruction.opcode < CodeConstants.opc_istore
          || instruction.opcode > CodeConstants.opc_astore_3) {
        continue;
      }
      for (int pc = instruction.startOffset; pc < instruction.startOffset + instruction.length; pc++) {
        Integer other = mapping.get(pc);
        if (other != null && other + 1 != line) {
          return true;
        }
      }
    }
    return false;
  }

  /** The instruction whose bytes cover {@code offset} in {@code method}, or null. */
  private static Instruction instructionAt(StructMethod method, StructClass cls, int offset) {
    if (method == null || cls == null) {
      return null;
    }
    FullInstructionSequence code = method.getInstructionSequence();
    if (code == null) {
      try {
        method.expandData(cls);
      }
      catch (Exception e) {
        return null;
      }
      code = method.getInstructionSequence();
    }
    if (code == null) {
      return null;
    }
    for (Instruction instruction : code) {
      if (offset >= instruction.startOffset && offset < instruction.startOffset + instruction.length) {
        return instruction;
      }
    }
    return null;
  }

  private static void candidate(Map<Integer, List<int[]>> candidates, int line, int shift, int exact,
      int offset) {
    candidates.computeIfAbsent(line, k -> new ArrayList<>()).add(new int[]{shift, exact, offset});
  }

  /**
   * Settles every line the method walk produced a constraint for.
   *
   * <p>A line whose instructions all agree keeps that shift. When they do not, the disagreement is
   * usually one instruction that inherited its line from an earlier LineNumberTable entry and is
   * printed on another line than the entry's own instruction: a chain link's receiver, or the store
   * of an expression spanning several lines. Such an inherited line describes the entry it came
   * from, not the text printed beside it. The instructions that have an entry of their own are the
   * ones whose text this printed line actually holds; a line still starts where the earliest of
   * them does, which is the statement's own line rather than an operand's continuation.
   */
  private static void resolveCandidates(Map<Integer, List<int[]>> candidates,
      TreeMap<Integer, Integer> shifts, Set<Integer> conflicted, Set<Integer> unmergeable,
      Set<Integer> inherited, Set<Integer> entryLines) {
    if (debug && System.getenv("NEUROFLOWER_LINEALIGN_CAND") != null) {
      for (Map.Entry<Integer, List<int[]>> e : candidates.entrySet()) {
        StringBuilder sb = new StringBuilder("cand L" + e.getKey() + " :");
        for (int[] c : e.getValue()) {
          sb.append(" {shift=").append(c[0]).append(", exact=").append(c[1]).append(", off=").append(c[2]).append('}');
        }
        System.err.println(sb);
      }
    }
    Integer previousExactTarget = null;
    for (Map.Entry<Integer, List<int[]>> line : candidates.entrySet()) {
      Set<Integer> all = new java.util.TreeSet<>();
      Set<Integer> exact = new java.util.TreeSet<>();
      for (int[] candidate : line.getValue()) {
        all.add(candidate[0]);
        if (candidate[1] != 0) {
          exact.add(candidate[0]);
        }
      }
      if (all.size() == 1) {
        if (exact.isEmpty()) {
          // The line carries no entry of its own: every offset on it inherits an earlier line,
          // which describes the expression the printer broke rather than this text. Text is
          // printed in source order, so an inherited target behind the last exact line's target
          // cannot be where this line sits: the record is stale and the line must neither anchor
          // the walk nor veto a join, or it drags the continuation back and blocks the merge the
          // text itself proves. A target at or after that line is consistent with the printed
          // order -- the gap is exactly the padding the table demands -- and stays an anchor.
          int shift = all.iterator().next();
          if (previousExactTarget == null || line.getKey() + shift >= previousExactTarget) {
            add(shifts, conflicted, line.getKey(), shift);
          }
          else {
            inherited.add(line.getKey());
            entryLines.remove(line.getKey());
          }
        }
        else {
          previousExactTarget = line.getKey() + all.iterator().next();
          add(shifts, conflicted, line.getKey(), all.iterator().next());
        }
      }
      else if (!exact.isEmpty()) {
        // The line's first token is the statement's start, and the instructions printed before
        // the operands that continue it carry the earliest original line among its own entries.
        // A javac line table may also place a statement's first instruction on the enclosing
        // construct's line -- a call's receiver load on the call's own line, or an expression
        // lambda's implicit return on the line the expression ends on. That entry belongs to the
        // smallest offset alone; when the remaining entries split across lines the text really
        // did span them, and one merged line cannot hold it.
        //
        // The first instruction on the printed line normally carries the line the statement
        // starts on, and the rest of the line follows it. javac may instead anchor that first
        // instruction on the line the *previous* text ended on -- the load a call prints before
        // its own text inherits the enclosing statement's line -- while a later instruction on
        // the same printed line (the call's own invoke) names the next source line. The printed
        // line then begins the later line, and the blank line between the two statements is paid
        // only when the line anchors there. When the first instruction names the line above and
        // entries after it agree on a later one, the earliest such later entry is the anchor;
        // when those entries split across lines, one merged line cannot hold them. Any other
        // shape keeps the earliest entry, which is where the text was written to start.
        int[] firstExact = null;
        for (int[] candidate : line.getValue()) {
          if (candidate[1] != 0 && (firstExact == null || candidate[2] < firstExact[2])) {
            firstExact = candidate;
          }
        }
        int floor = previousExactTarget == null ? Integer.MIN_VALUE : previousExactTarget;
        boolean splitByFirst = firstExact != null && previousExactTarget != null
          && line.getKey() + firstExact[0] == floor;
        boolean anchored = false;
        int chosenTarget = 0;
        int chosenShift = 0;
        if (splitByFirst) {
          for (int[] candidate : line.getValue()) {
            if (candidate[1] == 0) {
              continue;
            }
            int target = line.getKey() + candidate[0];
            if (target <= floor) {
              continue;
            }
            if (!anchored || target < chosenTarget) {
              anchored = true;
              chosenTarget = target;
              chosenShift = candidate[0];
            }
          }
        }
        if (anchored) {
          for (int[] candidate : line.getValue()) {
            if (candidate[1] != 0 && candidate != firstExact && line.getKey() + candidate[0] > floor
                && line.getKey() + candidate[0] != chosenTarget) {
              unmergeable.add(line.getKey());
              break;
            }
          }
        }
        else {
          // The line starts where its first entry says. A differing entry belongs to the smallest
          // offset alone -- a lambda's start marker or a call's own line -- and is tolerated; when
          // the remaining entries split across lines the text really did span them.
          if (exact.size() > 1) {
            int earliest = exact.iterator().next();
            for (int[] candidate : line.getValue()) {
              if (candidate[1] != 0 && candidate != firstExact && candidate[0] != earliest) {
                unmergeable.add(line.getKey());
                break;
              }
            }
          }
          Integer inheritedStart = exact.size() == 1 && !splitByFirst
            ? inheritedStartShift(line.getValue(), firstExact) : null;
          chosenShift = inheritedStart != null ? inheritedStart : exact.iterator().next();
          chosenTarget = line.getKey() + chosenShift;
        }
        previousExactTarget = chosenTarget;
        add(shifts, conflicted, line.getKey(), chosenShift);
      }
      else {
        shifts.remove(line.getKey());
        conflicted.add(line.getKey());
      }
    }
  }

  /**
   * Places the anchors one gap at a time: two consecutive anchors must be as many lines apart
   * as they are in the original. A gap that is too short gets padding before the later anchor;
   * one that is too long loses blank or joinable lines between them. Only when a method's own
   * anchors cannot pay a gap does the walk reclaim padding parked in an earlier gap.
   *
   * <p>Returns false when an insertion would fall inside a text block, in which case the buffer
   * must stay as printed.
   */
  private static boolean walkGaps(String[] lines, TreeMap<Integer, Integer> shifts,
      Set<Integer> unmergeable, Set<Integer> inherited, Set<Integer> entryLines,
      Set<Integer> joinBlocked, LineRecords records, List<int[]> inserts, List<Integer> removals,
      List<Integer> joins) {
    List<int[]> placed = new ArrayList<>(); // {index, paid shift, required shift}
    int previous = 0;
    int previousIndex = -1;
    for (Map.Entry<Integer, Integer> entry : shifts.entrySet()) {
      int index = entry.getKey() - 1;
      int desired = entry.getValue();
      if (index < 0 || index > lines.length) {
        return false;
      }
      int paid = desired;
      if (desired > previous) {
        if (insideTextBlock(lines, index)) {
          return false;
        }
        inserts.add(new int[]{index, desired - previous});
      }
      else if (desired < previous) {
        int want = previous - desired;
        int need = want;
        int lowest = previousIndex;
        for (int i = Math.min(index - 1, lines.length - 1); i > lowest && need > 0; i--) {
          if (removable(lines, i) && !removals.contains(i)) {
            removals.add(i);
            need--;
          }
        }
        // The anchor's own line is the first candidate: joining it onto the line above lifts the
        // anchor by one, which is exactly what a negative gap wants. It is an entry line itself,
        // so the entry-line veto is waived for it alone -- but only where the merge cannot put
        // the anchor's text on a line the table places somewhere else.
        if (!joinBlocked.contains(entry.getKey())) {
          for (int i = Math.min(index, lines.length - 1); i > lowest && need > 0; i--) {
            boolean anchorLine = i == index
              && selfJoinSafe(entry.getKey(), desired, shifts, unmergeable, inherited, entryLines);
            // A join moves line i onto line i-1, so neither may be a line another edit deletes.
            if (joinable(lines, i, entryLines, anchorLine)
                && joinRecordsSupport(i + 1, i, entry.getKey() + desired, records)
                && !removals.contains(i) && !removals.contains(i - 1) && !joins.contains(i)) {
              joins.add(i);
              need--;
            }
          }
        }
        if (need > 0) {
          need -= reclaim(lines, need, previousIndex, placed, removals, joins);
        }
        paid = previous - (want - need);
        if (debug && need > 0) {
          System.err.println("gap underpaid line " + entry.getKey() + " want " + want + " unpaid " + need
            + " from " + lowest + " to " + index);
        }
      }
      placed.add(new int[]{index, paid, desired});
      previous = paid;
      previousIndex = index;
    }
    return true;
  }

  /**
   * Deletes blank or padding lines from gaps before the previous anchor to pay a gap that has
   * nothing left of its own. Every anchor that follows a deleted line is lifted one line, so a
   * line may only be taken while all of them are still above their own targets: the lift then
   * moves them closer instead of past them. Returns how many lines were taken.
   */
  private static int reclaim(String[] lines, int need, int previousIndex, List<int[]> placed,
      List<Integer> removals, List<Integer> joins) {
    int found = 0;
    int anchor = placed.size() - 1;
    int limit = Integer.MAX_VALUE;
    for (int i = previousIndex - 1; i >= 0 && need > 0; i--) {
      while (anchor >= 0 && placed.get(anchor)[0] > i) {
        int[] entry = placed.get(anchor--);
        limit = Math.min(limit, entry[1] - entry[2]); // paid minus required: how far it can rise
      }
      if (limit <= 0) {
        break;
      }
      // A join planned on line i or i-1 claims this one; deleting it would take text with it.
      if (removable(lines, i) && !removals.contains(i)
          && !joins.contains(i) && !joins.contains(i + 1)) {
        removals.add(i);
        found++;
        need--;
        limit--;
        for (int k = anchor + 1; k < placed.size(); k++) {
          placed.get(k)[1]--;
        }
      }
    }
    return found;
  }

  /**
   * Whether the current anchor's own line may be joined onto the line above it.
   *
   * <p>Both printed lines become one source line, so the anchor's entry would move onto whatever
   * line the text above ends up on. Merging is harmless when the line above carries no entry of
   * its own: its text inherits a line, and the merged line settles on the anchor's target either
   * way. When it does carry an entry, the merge is only safe if that entry stands on the anchor's
   * own target line -- the source itself kept both texts on one line -- and the anchor's own shift
   * is backed by an entry rather than inherited: an inherited shift is a guess, and the walk's
   * underpayment is what places such a line correctly. An entry whose shift is unknown cannot
   * prove either.
   */
  private static boolean selfJoinSafe(int key, int desired, TreeMap<Integer, Integer> shifts,
      Set<Integer> unmergeable, Set<Integer> inherited, Set<Integer> entryLines) {
    if (unmergeable.contains(key)) {
      // The line's own entries sit on several source lines; no single merged line can hold them.
      return false;
    }
    // The line above the anchor is one-based line `key - 1`.
    int above = key - 1;
    if (!entryLines.contains(above)) {
      return true;
    }
    if (inherited.contains(key)) {
      // The line above carries an entry and the anchor's own shift is only inherited: the
      // walk's underpayment is what places it, and paying the gap by a merge would move the
      // text onto the line above's entry.
      return false;
    }
    Integer aboveShift = shifts.get(above);
    return aboveShift != null && aboveShift == desired + 1;
  }

  private static boolean joinable(String[] lines, int index, Set<Integer> entryLines, boolean anchorLine) {
    if (index <= 0 || index >= lines.length) {
      return false;
    }
    if (!anchorLine && entryLines.contains(index + 1)) {
      return false;
    }
    if (index == lines.length - 1 && lines[index].isEmpty()) {
      return false;
    }
    if (insideTextBlock(lines, index) || insideTextBlock(lines, index - 1)) {
      return false;
    }
    if (lines[index - 1].contains("//") || lines[index - 1].contains("/*") || lines[index].contains("*/")) {
      return false;
    }
    return !lines[index].trim().isEmpty();
  }

  private static boolean removable(String[] lines, int index) {
    if (index < 0 || index >= lines.length) {
      return false;
    }
    if (index == lines.length - 1 && lines[index].isEmpty()) {
      return false;
    }
    String trimmed = lines[index].trim();
    return (trimmed.isEmpty() || trimmed.equals(PADDING)) && !insideTextBlock(lines, index);
  }

  private static boolean insideTextBlock(String[] lines, int index) {
    int delimiters = 0;
    for (int i = 0; i < index && i < lines.length; i++) {
      int from = 0;
      while (true) {
        int at = lines[i].indexOf("\"\"\"", from);
        if (at < 0) {
          break;
        }
        delimiters++;
        from = at + 3;
      }
    }
    return delimiters % 2 == 1;
  }
}
