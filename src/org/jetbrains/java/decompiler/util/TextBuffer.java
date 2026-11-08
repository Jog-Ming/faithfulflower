/*
 * Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
 */
package org.jetbrains.java.decompiler.util;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.BytecodeMappingTracer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AnnotationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.TypeAnnotation;
import org.jetbrains.java.decompiler.struct.gen.FieldDescriptor;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Allows to connect text with resulting lines
 *
 * @author egor
 */
@SuppressWarnings("UnusedReturnValue")
public class TextBuffer {
  private static final boolean ALLOW_TO_STRING = Boolean.getBoolean("decompiler.allow.text.buffer.to.string");

  private final String myLineSeparator = DecompilerContext.getNewLineSeparator();
  private final String myIndent = (String)DecompilerContext.getProperty(IFernflowerPreferences.INDENT_STRING);
  private final int myPreferredLineLength = DecompilerContext.getIntOption(IFernflowerPreferences.PREFERRED_LINE_LENGTH);
  private final NewlineGroup myRootGroup = new NewlineGroup(null, 0, 0, 0);
  private NewlineGroup myCurrentGroup = myRootGroup;
  private boolean myHasReformatted = false;
  private final StringBuilder myStringBuilder;
  private Map<Integer, Integer> myLineToOffsetMapping = null;
  private final MappingStore myBytecodeOffsetMapping = new MappingStore(); // bytecode offset -> offset in text
  // Positions the line aligner uses that are not evidence for the constant-name pass: an anchor
  // the aligner needs must not join that pass's pool-order model.
  private final MappingStore myAlignOnlyMapping = new MappingStore(); // bytecode offset -> offset in text
  private final List<ClassRegion> myClassRegions = new ArrayList<>(); // text ranges a nested class was printed into
  private final Deque<ClassRegion> myOpenClassRegions = new ArrayDeque<>();
  private final DebugTrace myDebugTrace = DecompilerContext.getOption(IFernflowerPreferences.UNIT_TEST_MODE) ? new DebugTrace(this) : null;

  public TextBuffer() {
    myStringBuilder = new StringBuilder();
  }

  public TextBuffer(int size) {
    myStringBuilder = new StringBuilder(size);
  }

  public TextBuffer(String text) {
    myStringBuilder = new StringBuilder(text);
  }

  public TextBuffer append(String str) {
    myStringBuilder.append(str);
    return this;
  }

  public TextBuffer append(char ch) {
    myStringBuilder.append(ch);
    return this;
  }

  public TextBuffer append(int i) {
    myStringBuilder.append(i);
    return this;
  }

  public TextBuffer appendLineSeparator() {
    myStringBuilder.append(myLineSeparator);
    return this;
  }

  public TextBuffer appendIndent(int length) {
    while (length-- > 0) {
      append(myIndent);
    }
    return this;
  }

  public TextBuffer appendCastTypeName(VarType type, List<Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> typeAnnotations, Set<String> filter) {
    return appendCastTypeName(type, typeAnnotations, filter, false, true);
  }

  public TextBuffer appendCastTypeName(VarType type, List<Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> typeAnnotations, Set<String> filter, boolean vararg, boolean flush) {
    TypeAnnotation.appendCastTypeName(this, type, typeAnnotations, filter, vararg, flush);
    return this;
  }

  public TextBuffer appendCastTypeName(VarType type, List<Pair<Queue<TypeAnnotation.PathValue>, AnnotationExprent>> typeAnnotations, Set<String> filter, boolean vararg, boolean flush, boolean memberName) {
    TypeAnnotation.appendCastTypeName(this, type, typeAnnotations, filter, vararg, flush, memberName);
    return this;
  }

  public TextBuffer appendCastTypeName(VarType type) {
    return appendCastTypeName(ExprProcessor.getCastTypeName(type), type);
  }

  public TextBuffer appendCastTypeName(String castName, VarType type) {
    return append(castName);
  }

  public TextBuffer appendTypeName(VarType type) {
    return appendTypeName(ExprProcessor.getTypeName(type), type);
  }

  public TextBuffer appendTypeName(String name, VarType type) {
    return append(name);
  }

  public TextBuffer appendClass(String value, boolean declaration, String qualifiedName) {
    return append(value);
  }

  public TextBuffer appendField(String value, boolean declaration, String className, String name, String descriptor) {
    return appendField(value, declaration, className, name, FieldDescriptor.parseDescriptor(descriptor));
  }

  public TextBuffer appendField(String value, boolean declaration, String className, String name, FieldDescriptor descriptor) {
    return append(value);
  }

  public TextBuffer appendMethod(String value, boolean declaration, String className, String name, String descriptor) {
    return appendMethod(value, declaration, className, name, MethodDescriptor.parseDescriptor(descriptor));
  }

  public TextBuffer appendMethod(String value, boolean declaration, String className, String name, MethodDescriptor descriptor) {
    return append(value);
  }

  public TextBuffer appendVariable(String value, boolean declaration, boolean parameter, String className, String methodName, String methodDescriptor, int index, String name) {
    return appendVariable(value, declaration, parameter, className, methodName, MethodDescriptor.parseDescriptor(methodDescriptor), index, name);
  }

  public TextBuffer appendVariable(String value, boolean declaration, boolean parameter, String className, String methodName, MethodDescriptor methodDescriptor, int index, String name) {
    return append(value);
  }

  /**
   * Pushes a newline group.
   * <p>
   * {@link #appendPossibleNewline} normally works like append, adding its string argument to the buffer. However, if
   * the line is running out of space, this text may later be replaced with a newline (plus indents).
   * Possible newlines are grouped into newline groups. In a newline group, either none of the replacements are replaced
   * with newlines, or all of them are (never only some of them). Possible newlines should not be added outside a group.
   * The API works as if there were a stack of newline groups. This method pushes to the stack and
   * {@link #popNewlineGroup()} pops from it. After the full source code has been generated, {@link #reformat()} is
   * called to actually substitute the text.
   *
   * @param baseIndent The indent that has already been explicitly applied
   * @param extraIndent The indent to be added if this group is applied
   */
  public TextBuffer pushNewlineGroup(int baseIndent, int extraIndent) {
    NewlineGroup group = new NewlineGroup(myCurrentGroup, myStringBuilder.length(), baseIndent, extraIndent);
    myCurrentGroup.myChildren.add(group);
    myCurrentGroup = group;
    return this;
  }

  /**
   * If the current group is applied, add a newline here.
   */
  public TextBuffer appendPossibleNewline() {
    return appendPossibleNewline("");
  }

  /**
   * If the current group is applied, add a newline here. Otherwise, add the argument.
   */
  public TextBuffer appendPossibleNewline(String alternative) {
    return appendPossibleNewline(alternative, false);
  }

  /**
   * If the current group is applied, add a newline here. Otherwise, add the argument.
   * If {@code dedent} is true, the extra indent from this group is unapplied from this point on.
   */
  public TextBuffer appendPossibleNewline(String alternative, boolean dedent) {
    myCurrentGroup.myReplacements.add(new NewlineGroup.Replacement(myStringBuilder.length(), alternative.length(), dedent));
    return append(alternative);
  }

  public TextBuffer popNewlineGroup() {
    if (myCurrentGroup == myRootGroup) {
      throw new IllegalStateException("Cannot pop root group: " + this.convertToStringAndAllowDataDiscard());
    }
    assert myStringBuilder.length() >= myCurrentGroup.myStart;
    myCurrentGroup.myLength = myStringBuilder.length() - myCurrentGroup.myStart;
    myCurrentGroup = myCurrentGroup.myParent;
    return this;
  }

  public TextBuffer prepend(String s) {
    myStringBuilder.insert(0, s);
    shiftMapping(s.length());
    return this;
  }

  public TextBuffer enclose(String left, String right) {
    prepend(left);
    append(right);
    return this;
  }

  public TextBuffer encloseWithParens() {
    return enclose("(", ")");
  }

  public boolean containsOnlyWhitespaces() {
    for (int i = 0; i < myStringBuilder.length(); i++) {
      if (myStringBuilder.charAt(i) != ' ') {
        return false;
      }
    }
    return true;
  }

  public void addBytecodeMapping(int bytecodeOffset) {
    if (myDebugTrace != null) {
      myDebugTrace.myPreventDeletion = true;
    }
    myBytecodeOffsetMapping.add(bytecodeOffset, myStringBuilder.length());
  }

  /**
   * Records a position for the line aligner only. The constant-name pass rebuilds javac's pool
   * order from the printed positions, and an anchor whose text is not where the target's table
   * says it sits would move the model's nearest-item point; the aligner still needs the anchor,
   * so it is kept out of {@link #getBytecodePositions()}.
   */
  public void addAlignOnlyBytecodeMapping(int bytecodeOffset) {
    if (myDebugTrace != null) {
      myDebugTrace.myPreventDeletion = true;
    }
    myAlignOnlyMapping.add(bytecodeOffset, myStringBuilder.length());
  }

  public void addAlignOnlyBytecodeMapping(BitSet bytecodeOffsets) {
    if (bytecodeOffsets == null) {
      return;
    }
    for (int i = bytecodeOffsets.nextSetBit(0); i >= 0; i = bytecodeOffsets.nextSetBit(i + 1)) {
      addAlignOnlyBytecodeMapping(i);
    }
  }

  /**
   * Whether an earlier print already placed this offset in this buffer. A closing brace anchors
   * the jump the source's block ended with, but a statement the block printed (a written
   * `continue;`) owns that jump and its line; the brace must not claim it.
   */
  public boolean hasBytecodeMapping(int bytecodeOffset) {
    return myBytecodeOffsetMapping.containsUnresolved(bytecodeOffset);
  }

  public void addStartBytecodeMapping(int bytecodeOffset) {
    if (myDebugTrace != null) {
      myDebugTrace.myPreventDeletion = true;
    }
    myBytecodeOffsetMapping.addIfAbsent(bytecodeOffset, 0);
  }

  /**
   * Maps an offset to an earlier position of this buffer under a method's key. A constructor's
   * pc0 belongs to its declaration line, which no printed body expression maps.
   */
  public void addBytecodeMappingAt(int textOffset, int bytecodeOffset, String className, String methodKey) {
    if (myDebugTrace != null) {
      myDebugTrace.myPreventDeletion = true;
    }
    myBytecodeOffsetMapping.addIfAbsent(bytecodeOffset, className, methodKey, textOffset);
  }

  public void addBytecodeMapping(BitSet bytecodeOffsets) {
    if (bytecodeOffsets == null) {
      return;
    }
    for (int i = bytecodeOffsets.nextSetBit(0); i >= 0; i = bytecodeOffsets.nextSetBit(i + 1)) {
      addBytecodeMapping(i);
    }
  }

  public void addStartBytecodeMapping(BitSet bytecodeOffsets) {
    if (bytecodeOffsets == null) {
      return;
    }
    for (int i = bytecodeOffsets.nextSetBit(0); i >= 0; i = bytecodeOffsets.nextSetBit(i + 1)) {
      addStartBytecodeMapping(i);
    }
  }

  /**
   * Moves every already-mapped offset the predicate accepts to one text position. An instruction
   * can belong to a source line whose text it was not printed beside: javac gives a class-qualified
   * static call's argument loads the line the class name sits on, while the printer writes them
   * after the dot, and only the class-name text carries that line.
   */
  public void moveBytecodeMappings(java.util.function.IntPredicate select, int textOffset) {
    myBytecodeOffsetMapping.moveUnresolvedPositions(select, textOffset);
  }

  public void clearUnassignedBytecodeMappingData() {
    myBytecodeOffsetMapping.clearUnresolved();
  }

  /**
   * Marks where a nested class's source begins. The printer writes nested classes (member, local
   * and anonymous) into buffers that are appended into the enclosing class's text, so a pass that
   * needs to treat a class as a unit has to carry these ranges along with the text.
   */
  public int beginRegion(String className) {
    int start = myStringBuilder.length();
    myOpenClassRegions.push(new ClassRegion(className, start, start));
    return start;
  }

  /** Closes the region {@link #beginRegion} opened; safe to call from a finally block. */
  public void endRegion(String className, int start) {
    ClassRegion region = myOpenClassRegions.peek();
    if (region == null || region.getStart() != start || !region.getClassName().equals(className)) {
      return;
    }
    myOpenClassRegions.pop();
    region.setEnd(myStringBuilder.length());
    myClassRegions.add(region);
  }

  /** The nested-class text ranges recorded so far, in no particular order. */
  public List<ClassRegion> getClassRegions() {
    return Collections.unmodifiableList(myClassRegions);
  }

  /**
   * Every bytecode offset the printer mapped, grouped by class and method and expressed as the
   * character offset in the (reformatted) text. Keys without a class are dropped: they are resolved
   * only when their buffer is appended into a larger one.
   */
  public Map<Pair<String, String>, Map<Integer, Integer>> getBytecodePositions() {
    return myBytecodeOffsetMapping.toPositions();
  }

  public Map<Pair<String, String>, BytecodeMappingTracer> getTracers() {
    List<Integer> newlineOffsets = new ArrayList<>();
    for (int i = myStringBuilder.indexOf(myLineSeparator); i != -1; i = myStringBuilder.indexOf(myLineSeparator, i + 1)) {
      newlineOffsets.add(i);
    }
    return myBytecodeOffsetMapping.toTracers(myAlignOnlyMapping, newlineOffsets);
  }

  /**
   * Recursive reformatting of groups.
   * If the group's content would take you over the specified preferred line length, then the group is applied.
   *
   * - This algorithm usually ensures that if a group is applied, then all the group's parents in the tree are also
   *   applied. This tends to produce a nice structured output with well-placed potential newlines.
   * - The formatter keeps track of the offset as a result of the reformat at each character in the text buffer, and
   *   applies them to the bytecode offsets afterwards, so that the line number mappings don't get messed up.
   */
  private void reformatGroup(NewlineGroup group, List<Integer> offsetMapping, int extraIndent) {
    int offset = offsetMapping.get(group.myStart);
    int actualStart = group.myStart + offset;
    // Find the last newline before the start of this group, so we know how long the line already is
    int lastNewline = myStringBuilder.lastIndexOf(myLineSeparator, actualStart);
    int nextNewline = myStringBuilder.indexOf(myLineSeparator, actualStart);
    // Find the end of the first line of this group, if the group were to not be reformatted
    int firstPartEnd = nextNewline == -1 ? actualStart + group.myLength : Math.min(nextNewline, actualStart + group.myLength);
    // Go through all lines in the group, and find the longest one (without reformatting)
    int groupEndWithoutNewlines = lastNewline == -1 ? firstPartEnd : firstPartEnd - lastNewline;
    while (nextNewline != -1 && nextNewline <= actualStart + group.myLength) {
      int lineStart = nextNewline;
      int lineEnd = nextNewline = myStringBuilder.indexOf(myLineSeparator, nextNewline + 1);
      if (lineEnd == -1 || lineEnd > actualStart + group.myLength) {
        lineEnd = actualStart + group.myLength;
      }
      int lineLength = extraIndent + lineEnd - lineStart - myLineSeparator.length();
      if (lineLength > groupEndWithoutNewlines) {
        groupEndWithoutNewlines = lineLength;
      }
    }
    // If the longest line is longer than the preferred line length, then reformat the group
    boolean addNewLines = groupEndWithoutNewlines > myPreferredLineLength;

    int originalExtraIndent = extraIndent;
    // If we're reformatting this group, and not only its children, then apply extra indentation
    if (addNewLines && !group.myReplacements.isEmpty()) {
      extraIndent += group.myExtraIndent;
    }

    // Iterate over the children and replacements in one go rather than separately, because offsets need to be applied
    // from left to right
    int childrenIndex = 0;
    int replacementIndex = 0;
    for (int pos = group.myStart; pos <= group.myStart + group.myLength; pos++) {
      if (pos != group.myStart) {
        offsetMapping.add(offset);
      }
      assert offsetMapping.size() == pos + 1;

      // add extra indent after newlines
      if (pos + offset + myLineSeparator.length() < myStringBuilder.length() && myStringBuilder.substring(pos + offset, pos + offset + myLineSeparator.length()).equals(myLineSeparator)) {
        // not for blank lines
        if (!(pos + offset + myLineSeparator.length() * 2 < myStringBuilder.length()) || !myStringBuilder.substring(pos + offset + myLineSeparator.length(), pos + offset + myLineSeparator.length() * 2).equals(myLineSeparator)) {
          for (int i = 0; i < extraIndent; i++) {
            myStringBuilder.insert(pos + offset + myLineSeparator.length(), myIndent);
          }
          offset += myIndent.length() * extraIndent;
        }
      }

      // do multiple passes in an inner loop, as there could be arbitrarily many with the same offset
      // or replacements with offsets equal to the end position of a child group
      boolean anotherPass = true;
      while (anotherPass) {
        anotherPass = false;

        // replace replaceables with newlines
        if (addNewLines && replacementIndex < group.myReplacements.size() && pos == group.myReplacements.get(replacementIndex).myStart) {
          NewlineGroup.Replacement replacement = group.myReplacements.get(replacementIndex);
          myStringBuilder.replace(pos + offset, pos + offset + replacement.myLength, myLineSeparator);
          if (replacement.myDedent) {
            extraIndent = originalExtraIndent;
          }
          for (int i = 0; i < group.myBaseIndent + extraIndent; i++) {
            myStringBuilder.insert(pos + offset + myLineSeparator.length(), myIndent);
          }
          offset += myIndent.length() * (group.myBaseIndent + extraIndent) + myLineSeparator.length() - replacement.myLength;
          replacementIndex++;
          anotherPass = true;
        }
        // offset may have changed, update the offset mapping here because the child groups rely on the value being
        // correct in the list
        offsetMapping.set(offsetMapping.size() - 1, offset);

        // recursively iterate through child groups
        int currentPos = pos;
        if (childrenIndex < group.myChildren.size() && group.myChildren.get(childrenIndex).myStart == currentPos) {
          NewlineGroup child = group.myChildren.get(childrenIndex);
          reformatGroup(child, offsetMapping, extraIndent);
          offset = offsetMapping.get(offsetMapping.size() - 1);
          pos += child.myLength;
          childrenIndex++;
          anotherPass = true;
        }
      }
    }

    // update the offset value here because it might have changed when adding indents after existing newlines
    // the parent relies on the value being correct in the list
    offsetMapping.set(offsetMapping.size() - 1, offset);
  }


  public void reformat() {
    if (myCurrentGroup != myRootGroup) {
      throw new IllegalStateException("Cannot reformat while in a group");
    }
    if (myHasReformatted) {
      throw new IllegalStateException("Cannot reformat twice");
    }
    myHasReformatted = true;

    //myRootGroup.dump("");

    myRootGroup.myLength = myStringBuilder.length();

    // The walk only ever changes text when it applies a group, and a group is applied only when one
    // of its lines exceeds the preferred length. When no line can reach that bound, every offset it
    // computes stays zero, so skipping it leaves the text, the offset mappings and the class
    // regions exactly as the walk would have left them. The default preferred length is far above
    // any line the generator writes, so this is the path a default run takes.
    if (!mayApplyAnyGroup()) {
      return;
    }

    List<Integer> offsetMapping = new ArrayList<>(myStringBuilder.length());
    offsetMapping.add(0);
    reformatGroup(myRootGroup, offsetMapping, 0);

    myBytecodeOffsetMapping.mapPositions(offsetMapping);
    myAlignOnlyMapping.mapPositions(offsetMapping);
    for (ClassRegion region : myClassRegions) {
      int start = region.myStart;
      int end = region.myEnd;
      region.myStart = start + offsetMapping.get(start);
      region.myEnd = end + offsetMapping.get(end);
    }
  }

  /**
   * Whether {@link #reformatGroup} could apply any group in the tree.
   *
   * <p>A group is applied when its longest line exceeds {@link #myPreferredLineLength}, and the
   * walk measures a line from one separator start to the next or to the group's end, so a group's
   * value is at most the line's own length plus one separator (the first-line measurement of a
   * group that starts mid-line includes the separator that precedes it). If even that upper bound
   * stays within the limit, no group is applied, no extra indent is ever added, and therefore no
   * replacement or indent insertion can happen anywhere in the walk.
   */
  private boolean mayApplyAnyGroup() {
    int separatorLength = myLineSeparator.length();
    if (separatorLength == 0) {
      return true; // no line structure to reason about; let the walk decide
    }
    long limit = (long)myPreferredLineLength - separatorLength;
    int lineStart = 0;
    while (true) {
      int separator = myStringBuilder.indexOf(myLineSeparator, lineStart);
      if (separator < 0) {
        return myStringBuilder.length() - lineStart > limit;
      }
      if (separator - lineStart > limit) {
        return true;
      }
      lineStart = separator + separatorLength;
    }
  }

  public boolean contentEquals(String string) {
    return myStringBuilder.toString().equals(string);
  }

  public String convertToStringAndAllowDataDiscard() {
    if (myDebugTrace != null) {
      myDebugTrace.myPreventDeletion = false;
    }
    String original = myStringBuilder.toString();
    if (myLineToOffsetMapping == null || myLineToOffsetMapping.isEmpty()) {
      if (myLineMapping != null) {
        return addOriginalLineNumbers();
      }
      return original;
    }
    else {
      StringBuilder res = new StringBuilder();
      String[] srcLines = original.split(myLineSeparator);
      int currentLineStartOffset = 0;
      int currentLine = 0;
      int previousMarkLine = 0;
      int dumpedLines = 0;
      ArrayList<Integer> linesWithMarks = new ArrayList<>(myLineToOffsetMapping.keySet());
      Collections.sort(linesWithMarks);
      for (Integer markLine : linesWithMarks) {
        Integer markOffset = myLineToOffsetMapping.get(markLine);
        while (currentLine < srcLines.length) {
          String line = srcLines[currentLine];
          int lineEnd = currentLineStartOffset + line.length() + myLineSeparator.length();
          if (markOffset <= lineEnd) {
            int requiredLine = markLine - 1;
            int linesToAdd = requiredLine - dumpedLines;
            dumpedLines = requiredLine;
            appendLines(res, srcLines, previousMarkLine, currentLine, linesToAdd);
            previousMarkLine = currentLine;
            break;
          }
          currentLineStartOffset = lineEnd;
          currentLine++;
        }
      }
      if (previousMarkLine < srcLines.length) {
        appendLines(res, srcLines, previousMarkLine, srcLines.length, srcLines.length - previousMarkLine);
      }

      return res.toString();
    }
  }

  @Override
  public String toString() {
    if (!ALLOW_TO_STRING) {
      if (DecompilerContext.getOption(IFernflowerPreferences.UNIT_TEST_MODE)) {
        throw new AssertionError("Usage of TextBuffer.toString");
      } else {
        DecompilerContext.getLogger().writeMessage("Usage of TextBuffer.toString", IFernflowerLogger.Severity.WARN);
      }
    }
    return convertToStringAndAllowDataDiscard();
  }

  private String addOriginalLineNumbers() {
    StringBuilder sb = new StringBuilder();
    int lineStart = 0, lineEnd;
    int count = 0, length = myLineSeparator.length();
    while ((lineEnd = myStringBuilder.indexOf(myLineSeparator, lineStart)) > 0) {
      ++count;
      sb.append(myStringBuilder.substring(lineStart, lineEnd));
      Set<Integer> integers = myLineMapping.get(count);
      if (integers != null) {
        sb.append("//");
        for (Integer integer : integers) {
          sb.append(' ').append(integer);
        }
      }
      sb.append(myLineSeparator);
      lineStart = lineEnd + length;
    }
    if (lineStart < myStringBuilder.length()) {
      sb.append(myStringBuilder.substring(lineStart));
    }
    return sb.toString();
  }

  private void appendLines(StringBuilder res, String[] srcLines, int from, int to, int requiredLineNumber) {
    if (to - from > requiredLineNumber) {
      List<String> strings = compactLines(Arrays.asList(srcLines).subList(from, to) ,requiredLineNumber);
      int separatorsRequired = requiredLineNumber - 1;
      for (String s : strings) {
        res.append(s);
        if (separatorsRequired-- > 0) {
          res.append(myLineSeparator);
        }
      }
      res.append(myLineSeparator);
    }
    else if (to - from <= requiredLineNumber) {
      for (int i = from; i < to; i++) {
        res.append(srcLines[i]).append(myLineSeparator);
      }
      for (int i = 0; i < requiredLineNumber - to + from; i++) {
        res.append(myLineSeparator);
      }
    }
  }

  public int length() {
    return myStringBuilder.length();
  }

  /**
   * Maps an offset at the last character already printed rather than at the buffer's end: a
   * jump the source wrote after a block's closing brace gets that brace's line, and the brace is
   * this buffer's last token.
   */
  public void addBytecodeMappingAtLastToken(int bytecodeOffset) {
    for (int i = myStringBuilder.length() - 1; i >= 0; i--) {
      if (!Character.isWhitespace(myStringBuilder.charAt(i))) {
        myBytecodeOffsetMapping.add(bytecodeOffset, i);
        return;
      }
    }
  }

  /**
   * The text position this buffer's own print gave a bytecode offset, or -1. A keyed position is
   * ignored: it was recorded by an enclosing buffer, not by the text this buffer holds.
   */
  public int ownBytecodeMappingPosition(int bytecodeOffset) {
    return myBytecodeOffsetMapping.unresolvedPosition(bytecodeOffset);
  }

  /**
   * Whether the printed line the position sits on holds a {@code return} statement. Such a
   * statement stands on the source line javac records for its instruction; moving the anchor to
   * a brace would shift it. The position may sit before the keyword (an exprent maps its text
   * start) or after it, so the whole line is read.
   */
  public boolean lineHoldsReturnAt(int position) {
    int at = Math.min(position, myStringBuilder.length());
    int start = at;
    while (start > 0 && myStringBuilder.charAt(start - 1) != '\n'
        && myStringBuilder.charAt(start - 1) != '\r') {
      start--;
    }
    int end = at;
    while (end < myStringBuilder.length() && myStringBuilder.charAt(end) != '\n'
        && myStringBuilder.charAt(end) != '\r') {
      end++;
    }
    return myStringBuilder.substring(start, end).contains("return");
  }

  /** The last character printed that is not whitespace, or ' ' when the buffer is blank. */
  public char lastTokenChar() {
    for (int i = myStringBuilder.length() - 1; i >= 0; i--) {
      char ch = myStringBuilder.charAt(i);
      if (!Character.isWhitespace(ch)) {
        return ch;
      }
    }
    return ' ';
  }

  public void setStart(int position) {
    myStringBuilder.delete(0, position);
    shiftMapping(-position);
  }

  public void setLength(int position) {
    myStringBuilder.setLength(position);
    myClassRegions.removeIf(region -> region.myStart >= position);
    for (ClassRegion region : myClassRegions) {
      if (region.myEnd > position) {
        region.myEnd = position;
      }
    }
    if (myLineToOffsetMapping != null) {
      Map<Integer, Integer> newMap = new HashMap<>();
      for (Map.Entry<Integer, Integer> entry : myLineToOffsetMapping.entrySet()) {
        if (entry.getValue() <= position) {
          newMap.put(entry.getKey(), entry.getValue());
        }
      }
      myLineToOffsetMapping = newMap;
    }
    myRootGroup.truncate(position);
    assert currentGroupExists();
  }

  private boolean currentGroupExists() {
    for (NewlineGroup group = myCurrentGroup; group != myRootGroup; group = group.myParent) {
      if (!group.myParent.myChildren.contains(group)) {
        return false;
      }
    }
    return true;
  }

  public TextBuffer append(TextBuffer buffer, String className, String methodKey) {
    if (buffer.myCurrentGroup != buffer.myRootGroup) {
      throw new IllegalArgumentException("Can't append buffer with non-root group");
    }
    if (buffer.myDebugTrace != null) {
      buffer.myDebugTrace.myPreventDeletion = false;
    }
    if (buffer.myLineToOffsetMapping != null && !buffer.myLineToOffsetMapping.isEmpty()) {
      checkMapCreated();
      for (Map.Entry<Integer, Integer> entry : buffer.myLineToOffsetMapping.entrySet()) {
        myLineToOffsetMapping.put(entry.getKey(), entry.getValue() + myStringBuilder.length());
      }
    }
    int textBase = myStringBuilder.length();
    myBytecodeOffsetMapping.append(buffer.myBytecodeOffsetMapping, className, methodKey, textBase);
    myAlignOnlyMapping.append(buffer.myAlignOnlyMapping, className, methodKey, textBase);
    NewlineGroup otherRoot = buffer.myRootGroup.copy();
    otherRoot.shift(myStringBuilder.length());
    myCurrentGroup.myReplacements.addAll(otherRoot.myReplacements);
    myCurrentGroup.myChildren.addAll(otherRoot.myChildren);
    int base = myStringBuilder.length();
    for (ClassRegion region : buffer.myClassRegions) {
      myClassRegions.add(new ClassRegion(region.myClassName, region.myStart + base, region.myEnd + base));
    }
    myStringBuilder.append(buffer.myStringBuilder);
    return this;
  }

  public TextBuffer append(TextBuffer buffer) {
    return append(buffer, null, null);
  }

  private void shiftMapping(int shiftOffset) {
    if (shiftOffset != 0) {
      for (Iterator<ClassRegion> itr = myClassRegions.iterator(); itr.hasNext(); ) {
        ClassRegion region = itr.next();
        region.myStart += shiftOffset;
        region.myEnd += shiftOffset;
        if (region.myEnd <= 0) {
          itr.remove();
        } else if (region.myStart < 0) {
          region.myStart = 0;
        }
      }
    }
    if (myLineToOffsetMapping != null) {
      Map<Integer, Integer> newMap = new HashMap<>();
      for (Map.Entry<Integer, Integer> entry : myLineToOffsetMapping.entrySet()) {
        int newValue = entry.getValue();
        if (newValue >= 0) {
          newValue += shiftOffset;
        }
        if (newValue >= 0) {
          newMap.put(entry.getKey(), newValue);
        }
      }
      myLineToOffsetMapping = newMap;
    }
    // A prefix removal can put a mapping before the buffer's start (the lambda path strips the
    // `return` of an expression body). The text it referred to is gone, so the mapping belongs
    // at the new start; a negative position would resolve inside the preceding text instead.
    myBytecodeOffsetMapping.shift(shiftOffset);
    myAlignOnlyMapping.shift(shiftOffset);
    myRootGroup.shift(shiftOffset);
  }

  private void checkMapCreated() {
    if (myLineToOffsetMapping == null) {
      myLineToOffsetMapping = new HashMap<>();
    }
  }

  public int countLines() {
    return countLines(0);
  }

  public int countLines(int from) {
    return count(myLineSeparator, from);
  }

  public int count(String substring, int from) {
    int count = 0, length = substring.length(), p = from;
    while ((p = myStringBuilder.indexOf(substring, p)) > 0) {
      ++count;
      p += length;
    }
    return count;
  }

  @Deprecated
  public int countChars(char c) {
    convertToStringAndAllowDataDiscard();

    int count = 0;

    CharSequence chars = myStringBuilder.subSequence(0, myStringBuilder.length());
    for (int i = 0; i < chars.length(); i++) {
      if (chars.charAt(i) == c) {
        count++;
      }
    }

    return count;
  }

  private static List<String> compactLines(List<String> srcLines, int requiredLineNumber) {
    if (srcLines.size() < 2 || srcLines.size() <= requiredLineNumber) {
      return srcLines;
    }
    List<String> res = new LinkedList<>(srcLines);
    // first join lines with a single { or }
    for (int i = res.size()-1; i > 0 ; i--) {
      String s = res.get(i);
      if (s.trim().equals("{") || s.trim().equals("}")) {
        res.set(i-1, res.get(i-1).concat(s));
        res.remove(i);
      }
      if (res.size() <= requiredLineNumber) {
        return res;
      }
    }
    // now join empty lines
    for (int i = res.size()-1; i > 0 ; i--) {
      String s = res.get(i);
      if (s.trim().isEmpty()) {
        res.set(i-1, res.get(i-1).concat(s));
        res.remove(i);
      }
      if (res.size() <= requiredLineNumber) {
        return res;
      }
    }
    return res;
  }

  private Map<Integer, Set<Integer>> myLineMapping = null; // new to original

  public void dumpOriginalLineNumbers(int[] lineMapping) {
    if (lineMapping.length > 0) {
      myLineMapping = new HashMap<>();
      for (int i = 0; i < lineMapping.length; i += 2) {
        int key = lineMapping[i + 1];
        Set<Integer> existing = myLineMapping.computeIfAbsent(key, k -> new TreeSet<>());
        existing.add(lineMapping[i]);
      }
    }
  }

  /** A nested class's text range; nested regions are contained in their enclosing region. */
  public static final class ClassRegion {
    private final String myClassName;
    private int myStart;
    private int myEnd;

    ClassRegion(String className, int start, int end) {
      myClassName = className;
      myStart = start;
      myEnd = end;
    }

    public String getClassName() {
      return myClassName;
    }

    public int getStart() {
      return myStart;
    }

    public int getEnd() {
      return myEnd;
    }

    private void setEnd(int end) {
      myEnd = end;
    }
  }

  /**
   * Insertion-ordered mapping from bytecode offsets to text positions, grouped by the class and
   * method that own the offsets.
   *
   * <p>The printer writes each method body into its own buffer, recording its offsets without a
   * class or method; appending that buffer into the class's buffer is what names the owner. One
   * ordered entry array per class and method lets that append move a whole method's entries with
   * array copies instead of one hash-map insertion per entry. The flat insertion order the readers
   * rely on is reproduced by the per-group order plus the order in which the groups were created.
   */
  private static final class MappingStore {
    private final LinkedHashMap<GroupKey, MappingGroup> myGroups = new LinkedHashMap<>();
    // Offsets recorded without a class or method; the unresolved group takes the appended buffer's
    // class and method when it is appended, and stays unresolved when that class is null.
    private MappingGroup myUnresolvedGroup;
    private int myNextSeq; // insertion sequence of the next new entry

    void add(int bytecodeOffset, int textOffset) {
      MappingGroup group = myUnresolvedGroup;
      if (group == null) {
        group = new MappingGroup(myNextSeq);
        myUnresolvedGroup = group;
      }
      if (group.put(bytecodeOffset, textOffset, myNextSeq)) {
        myNextSeq++;
      }
    }

    void addIfAbsent(int bytecodeOffset, int textOffset) {
      MappingGroup group = myUnresolvedGroup;
      if (group == null) {
        group = new MappingGroup(myNextSeq);
        myUnresolvedGroup = group;
      }
      if (group.putIfAbsent(bytecodeOffset, textOffset, myNextSeq)) {
        myNextSeq++;
      }
    }

    void addIfAbsent(int bytecodeOffset, String className, String methodKey, int textOffset) {
      if (className == null) {
        addIfAbsent(bytecodeOffset, textOffset);
        return;
      }
      GroupKey key = new GroupKey(className, methodKey);
      MappingGroup group = myGroups.get(key);
      if (group == null) {
        group = new MappingGroup(myNextSeq);
        myGroups.put(key, group);
      }
      if (group.putIfAbsent(bytecodeOffset, textOffset, myNextSeq)) {
        myNextSeq++;
      }
    }

    boolean containsUnresolved(int bytecodeOffset) {
      return myUnresolvedGroup != null && myUnresolvedGroup.find(bytecodeOffset) >= 0;
    }

    int unresolvedPosition(int bytecodeOffset) {
      if (myUnresolvedGroup == null) {
        return -1;
      }
      int slot = myUnresolvedGroup.find(bytecodeOffset);
      return slot < 0 ? -1 : myUnresolvedGroup.myPositions[slot];
    }

    void moveUnresolvedPositions(java.util.function.IntPredicate select, int textOffset) {
      if (myUnresolvedGroup == null) {
        return;
      }
      MappingGroup group = myUnresolvedGroup;
      for (int i = 0; i < group.mySize; i++) {
        if (select.test(group.myOffsets[i])) {
          group.myPositions[i] = textOffset;
        }
      }
    }

    void clearUnresolved() {
      myUnresolvedGroup = null;
    }

    Map<Pair<String, String>, Map<Integer, Integer>> toPositions() {
      Map<Pair<String, String>, Map<Integer, Integer>> positions = new LinkedHashMap<>();
      for (Map.Entry<GroupKey, MappingGroup> entry : myGroups.entrySet()) {
        GroupKey key = entry.getKey();
        if (key.myMethod == null) {
          continue;
        }
        MappingGroup group = entry.getValue();
        Map<Integer, Integer> method = positions.computeIfAbsent(Pair.of(key.myClass, key.myMethod), k -> new LinkedHashMap<>());
        for (int i = 0; i < group.mySize; i++) {
          method.put(group.myOffsets[i], group.myPositions[i]);
        }
      }
      return positions;
    }

    Map<Pair<String, String>, BytecodeMappingTracer> toTracers(MappingStore alignOnly, List<Integer> newlineOffsets) {
      Map<Pair<String, String>, BytecodeMappingTracer> tracers = new LinkedHashMap<>();
      if (myUnresolvedGroup != null || alignOnly.myUnresolvedGroup != null) {
        throw new IllegalStateException("getTracers called when not all bytecode offsets have a valid class and method");
      }
      // A position recorded in both maps uses the align-only text offset, at the bytecode map's
      // place in the order; the flags let the align-only pass skip those entries.
      Map<GroupKey, boolean[]> matchedAlign = new LinkedHashMap<>();
      for (Map.Entry<GroupKey, MappingGroup> entry : myGroups.entrySet()) {
        GroupKey key = entry.getKey();
        MappingGroup group = entry.getValue();
        MappingGroup alignGroup = alignOnly.myGroups.get(key);
        boolean[] matched = null;
        if (alignGroup != null) {
          matched = new boolean[alignGroup.mySize];
          matchedAlign.put(key, matched);
        }
        Pair<String, String> pair = Pair.of(key.myClass, key.myMethod);
        BytecodeMappingTracer tracer = null;
        for (int i = 0; i < group.mySize; i++) {
          int textOffset = group.myPositions[i];
          if (alignGroup != null) {
            int slot = alignGroup.find(group.myOffsets[i]);
            if (slot >= 0) {
              textOffset = alignGroup.myPositions[slot];
              matched[slot] = true;
            }
          }
          if (tracer == null) {
            tracer = tracers.get(pair);
            if (tracer == null) {
              tracer = new BytecodeMappingTracer();
              tracers.put(pair, tracer);
            }
          }
          tracer.setCurrentSourceLine(lineAt(newlineOffsets, textOffset));
          tracer.addMapping(group.myOffsets[i]);
        }
      }
      for (Map.Entry<GroupKey, MappingGroup> entry : alignOnly.myGroups.entrySet()) {
        GroupKey key = entry.getKey();
        MappingGroup group = entry.getValue();
        boolean[] matched = matchedAlign.get(key);
        Pair<String, String> pair = Pair.of(key.myClass, key.myMethod);
        BytecodeMappingTracer tracer = null;
        for (int i = 0; i < group.mySize; i++) {
          if (matched != null && matched[i]) {
            continue;
          }
          if (tracer == null) {
            tracer = tracers.get(pair);
            if (tracer == null) {
              tracer = new BytecodeMappingTracer();
              tracers.put(pair, tracer);
            }
          }
          tracer.setCurrentSourceLine(lineAt(newlineOffsets, group.myPositions[i]));
          tracer.addMapping(group.myOffsets[i]);
        }
      }
      return tracers;
    }

    private static int lineAt(List<Integer> newlineOffsets, int textOffset) {
      int lineNo = Collections.binarySearch(newlineOffsets, textOffset);
      return lineNo < 0 ? -lineNo - 1 : lineNo;
    }

    /**
     * Merges the source's entries into this store. The source's unresolved offsets take the class
     * and method of the appended buffer; an entry whose target key already has its offset keeps
     * the target's position, exactly as the per-entry putIfAbsent this replaces did.
     */
    void append(MappingStore source, String className, String methodKey, int textBase) {
      if (source.myGroups.isEmpty() && source.myUnresolvedGroup == null) {
        return;
      }
      // Groups in the order their first entry was recorded. Named groups already are; the
      // unresolved group is inserted at its creation point.
      List<GroupKey> keys = new ArrayList<>(source.myGroups.size() + 1);
      List<MappingGroup> groups = new ArrayList<>(source.myGroups.size() + 1);
      for (Map.Entry<GroupKey, MappingGroup> entry : source.myGroups.entrySet()) {
        keys.add(entry.getKey());
        groups.add(entry.getValue());
      }
      if (source.myUnresolvedGroup != null) {
        int at = 0;
        while (at < groups.size() && groups.get(at).myCreationSeq < source.myUnresolvedGroup.myCreationSeq) {
          at++;
        }
        keys.add(at, className == null ? null : new GroupKey(className, methodKey));
        groups.add(at, source.myUnresolvedGroup);
      }
      // Several source groups can resolve to one target key (the unresolved group and a group the
      // source already named). They are merged together, earliest sequence first.
      Map<GroupKey, List<MappingGroup>> byKey = new LinkedHashMap<>();
      for (int i = 0; i < keys.size(); i++) {
        byKey.computeIfAbsent(keys.get(i), k -> new ArrayList<>()).add(groups.get(i));
      }
      int seqShift = myNextSeq;
      for (Map.Entry<GroupKey, List<MappingGroup>> entry : byKey.entrySet()) {
        GroupKey key = entry.getKey();
        List<MappingGroup> sources = entry.getValue();
        MappingGroup target = key == null ? myUnresolvedGroup : myGroups.get(key);
        if (target == null) {
          target = new MappingGroup(seqShift + sources.get(0).myCreationSeq);
          if (key == null) {
            myUnresolvedGroup = target;
          } else {
            myGroups.put(key, target);
          }
          if (sources.size() == 1) {
            target.copyFrom(sources.get(0), textBase, seqShift);
            continue;
          }
        }
        mergeInto(target, sources, textBase, seqShift);
      }
      myNextSeq = seqShift + source.myNextSeq;
    }

    private static void mergeInto(MappingGroup target, List<MappingGroup> sources, int textBase, int seqShift) {
      if (sources.size() == 1) {
        MappingGroup source = sources.get(0);
        for (int i = 0; i < source.mySize; i++) {
          target.putIfAbsent(source.myOffsets[i], source.myPositions[i] + textBase, source.mySeqs[i] + seqShift);
        }
        return;
      }
      // The groups' own offsets are unique, but an offset can occur in two of them. Their
      // insertion sequences decide which comes first.
      int[] pointers = new int[sources.size()];
      while (true) {
        int next = -1;
        int nextSeq = Integer.MAX_VALUE;
        for (int i = 0; i < sources.size(); i++) {
          MappingGroup group = sources.get(i);
          if (pointers[i] < group.mySize && group.mySeqs[pointers[i]] < nextSeq) {
            next = i;
            nextSeq = group.mySeqs[pointers[i]];
          }
        }
        if (next < 0) {
          return;
        }
        MappingGroup group = sources.get(next);
        int slot = pointers[next]++;
        target.putIfAbsent(group.myOffsets[slot], group.myPositions[slot] + textBase, group.mySeqs[slot] + seqShift);
      }
    }

    void mapPositions(List<Integer> offsetMapping) {
      if (myUnresolvedGroup != null) {
        myUnresolvedGroup.mapPositions(offsetMapping);
      }
      for (MappingGroup group : myGroups.values()) {
        group.mapPositions(offsetMapping);
      }
    }

    void shift(int shiftOffset) {
      if (shiftOffset == 0) {
        return;
      }
      if (myUnresolvedGroup != null) {
        myUnresolvedGroup.shift(shiftOffset);
      }
      for (MappingGroup group : myGroups.values()) {
        group.shift(shiftOffset);
      }
    }
  }

  /** The class and method that own a group of bytecode offsets. */
  private static final class GroupKey {
    private final String myClass;
    private final String myMethod;
    private final int myHash;

    GroupKey(String className, String methodKey) {
      myClass = className;
      myMethod = methodKey;
      myHash = className.hashCode() * 31 + Objects.hashCode(methodKey);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      GroupKey that = (GroupKey)o;
      return myClass.equals(that.myClass) && Objects.equals(myMethod, that.myMethod);
    }

    @Override
    public int hashCode() {
      return myHash;
    }
  }

  /**
   * One class and method's offsets in insertion order, with an offset index built on first
   * lookup. Entries are appended, never inserted in the middle; overwriting an offset keeps its
   * place, as the insertion-ordered map this replaces did.
   */
  private static final class MappingGroup {
    private int[] myOffsets = InterpreterUtil.EMPTY_INT_ARRAY;
    private int[] myPositions = InterpreterUtil.EMPTY_INT_ARRAY;
    private int[] mySeqs = InterpreterUtil.EMPTY_INT_ARRAY;
    private int mySize;
    private final int myCreationSeq;
    private int[] myIndex; // offset -> slot + 1; 0 marks a free bucket

    MappingGroup(int creationSeq) {
      myCreationSeq = creationSeq;
    }

    int find(int bytecodeOffset) {
      if (myIndex == null) {
        buildIndex();
      }
      return indexFind(bytecodeOffset);
    }

    boolean put(int bytecodeOffset, int textOffset, int seq) {
      if (myIndex == null) {
        buildIndex();
      }
      int slot = indexFind(bytecodeOffset);
      if (slot >= 0) {
        myPositions[slot] = textOffset;
        return false;
      }
      insert(bytecodeOffset, textOffset, seq);
      return true;
    }

    boolean putIfAbsent(int bytecodeOffset, int textOffset, int seq) {
      if (myIndex == null) {
        buildIndex();
      }
      if (indexFind(bytecodeOffset) >= 0) {
        return false;
      }
      insert(bytecodeOffset, textOffset, seq);
      return true;
    }

    void copyFrom(MappingGroup source, int textBase, int seqShift) {
      int size = source.mySize;
      myOffsets = new int[size];
      myPositions = new int[size];
      mySeqs = new int[size];
      System.arraycopy(source.myOffsets, 0, myOffsets, 0, size);
      if (textBase == 0) {
        System.arraycopy(source.myPositions, 0, myPositions, 0, size);
      } else {
        for (int i = 0; i < size; i++) {
          myPositions[i] = source.myPositions[i] + textBase;
        }
      }
      if (seqShift == 0) {
        System.arraycopy(source.mySeqs, 0, mySeqs, 0, size);
      } else {
        for (int i = 0; i < size; i++) {
          mySeqs[i] = source.mySeqs[i] + seqShift;
        }
      }
      mySize = size;
    }

    void mapPositions(List<Integer> offsetMapping) {
      for (int i = 0; i < mySize; i++) {
        int position = myPositions[i];
        myPositions[i] = position + offsetMapping.get(position);
      }
    }

    void shift(int shiftOffset) {
      for (int i = 0; i < mySize; i++) {
        myPositions[i] = Math.max(0, myPositions[i] + shiftOffset);
      }
    }

    private void insert(int bytecodeOffset, int textOffset, int seq) {
      if (mySize == myOffsets.length) {
        grow();
      }
      int slot = mySize++;
      myOffsets[slot] = bytecodeOffset;
      myPositions[slot] = textOffset;
      mySeqs[slot] = seq;
      if (mySize * 2 > myIndex.length) {
        buildIndex();
      } else {
        addToIndex(slot);
      }
    }

    private void grow() {
      int capacity = Math.max(4, myOffsets.length * 2);
      myOffsets = Arrays.copyOf(myOffsets, capacity);
      myPositions = Arrays.copyOf(myPositions, capacity);
      mySeqs = Arrays.copyOf(mySeqs, capacity);
    }

    private void buildIndex() {
      int capacity = 4;
      while (capacity < mySize * 2) {
        capacity <<= 1;
      }
      myIndex = new int[capacity];
      for (int i = 0; i < mySize; i++) {
        addToIndex(i);
      }
    }

    private void addToIndex(int slot) {
      int mask = myIndex.length - 1;
      int bucket = mix(myOffsets[slot]) & mask;
      while (myIndex[bucket] != 0) {
        bucket = (bucket + 1) & mask;
      }
      myIndex[bucket] = slot + 1;
    }

    private int indexFind(int bytecodeOffset) {
      int mask = myIndex.length - 1;
      int bucket = mix(bytecodeOffset) & mask;
      while (true) {
        int slot = myIndex[bucket];
        if (slot == 0) {
          return -1;
        }
        if (myOffsets[slot - 1] == bytecodeOffset) {
          return slot - 1;
        }
        bucket = (bucket + 1) & mask;
      }
    }

    private static int mix(int value) {
      value ^= value >>> 16;
      value *= 0x7feb352d;
      value ^= value >>> 15;
      return value;
    }
  }

  private static final class NewlineGroup {
    final NewlineGroup myParent;
    int myStart;
    int myLength;
    final int myBaseIndent;
    final int myExtraIndent;
    final List<NewlineGroup> myChildren = new ArrayList<>();
    final List<Replacement> myReplacements = new ArrayList<>();

    NewlineGroup(NewlineGroup parent, int start, int baseIndent, int extraIndent) {
      this.myParent = parent;
      this.myStart = start;
      this.myBaseIndent = baseIndent;
      this.myExtraIndent = extraIndent;
    }

    void shift(int amount) {
      myStart += amount;
      for (Replacement replacement : myReplacements) {
        replacement.myStart += amount;
      }
      for (NewlineGroup child : myChildren) {
        child.shift(amount);
      }
    }

    void truncate(int stringLength) {
      if (myStart + myLength > stringLength) {
        myLength = stringLength - myStart;
      }
      for (Iterator<NewlineGroup> itr = myChildren.iterator(); itr.hasNext(); ) {
        NewlineGroup child = itr.next();
        if (child.myStart <= stringLength) {
          child.truncate(stringLength);
        } else {
          itr.remove();
        }
      }
      myReplacements.removeIf(r -> r.myStart > stringLength);
    }

    void dump(String indent) {
      System.out.println(indent + "group " + myStart + "-" + (myStart + myLength) + ": " + myReplacements.size() + " replacements");
      for (NewlineGroup child : myChildren) {
        child.dump(indent + "  ");
      }
    }

    NewlineGroup copy() {
      NewlineGroup copy = new NewlineGroup(myParent, myStart, myBaseIndent, myExtraIndent);
      copy.myLength = myLength;
      for (NewlineGroup child : myChildren) {
        copy.myChildren.add(child.copy());
      }
      copy.myReplacements.addAll(myReplacements);
      return copy;
    }

    private static class Replacement {
      int myStart;
      final int myLength;
      final boolean myDedent;

      Replacement(int start, int length, boolean dedent) {
        this.myStart = start;
        this.myLength = length;
        this.myDedent = dedent;
      }
    }
  }

  public static void checkLeaks() {
    DebugTrace.checkLeaks();
  }

  // it's really important that this class does not directly or indirectly reference the TextBuffer, or we will create memory leaks
  static class DebugTrace extends WeakReference<TextBuffer> {
    private static final Set<DebugTrace> ALL_REMAINING_TRACES = ConcurrentHashMap.newKeySet();

    private static final AtomicBoolean STARTED = new AtomicBoolean();
    private static final ReferenceQueue<TextBuffer> REFERENCE_QUEUE = new ReferenceQueue<>();

    private static void ensureStarted() {
      if (!STARTED.getAndSet(true)) {
        Thread cleaner = new Thread(() -> {
          while (true) {
            DebugTrace trace;
            try {
              trace = (DebugTrace) REFERENCE_QUEUE.remove();
            } catch (InterruptedException e) {
              break;
            }
            trace.onDeletion();
            ALL_REMAINING_TRACES.remove(trace);
          }
        });
        cleaner.setName("TextBuffer debug cleaner");
        cleaner.setDaemon(true);
        cleaner.start();
      }
    }

    DebugTrace(TextBuffer buffer) {
      super(buffer, REFERENCE_QUEUE);
      ensureStarted();
      ALL_REMAINING_TRACES.add(this);
    }

    final Throwable myCreationTrace = new Throwable();
    boolean myPreventDeletion = false;

    private void onDeletion() {
      if (myPreventDeletion && (!DotExporter.DUMP_DOTS && !DotExporter.DUMP_ERROR_DOTS)) {
        throw new AssertionError(
          "TextBuffer was garbage collected without being added to another TextBuffer, data loss occurred. See cause for the creation trace",
          myCreationTrace
        );
      }
    }

    static void checkLeaks() {
      for (DebugTrace trace : ALL_REMAINING_TRACES) {
        trace.onDeletion();
      }
      ALL_REMAINING_TRACES.clear();
    }
  }
}