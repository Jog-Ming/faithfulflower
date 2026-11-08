// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.attr;

import org.jetbrains.java.decompiler.code.BytecodeVersion;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.util.DataInputFullStream;
import org.jetbrains.java.decompiler.util.InterpreterUtil;

import java.io.IOException;

/**
 * u2 line_number_table_length;
 * {  u2 start_pc;
 *    u2 line_number;
 * } line_number_table[line_number_table_length];
 *
 * Created by Egor on 05.10.2014.
 */
public class StructLineNumberTableAttribute extends StructGeneralAttribute {
  private int[] myLineInfo = InterpreterUtil.EMPTY_INT_ARRAY;
  /** Whether {@link #myLineInfo}'s start_pc values are non-decreasing; false means use the walk. */
  private boolean myLineInfoSorted;

  @Override
  public void initContent(DataInputFullStream data, ConstantPool pool, BytecodeVersion version) throws IOException {
    int len = data.readUnsignedShort() * 2;
    if (len > 0) {
      myLineInfo = new int[len];
      for (int i = 0; i < len; i += 2) {
        myLineInfo[i] = data.readUnsignedShort();
        myLineInfo[i + 1] = data.readUnsignedShort();
      }
      myLineInfoSorted = isSortedByStartPc(myLineInfo);
    }
    else if (myLineInfo.length > 0) {
      myLineInfo = InterpreterUtil.EMPTY_INT_ARRAY;
      myLineInfoSorted = false;
    }
  }

  public int findLineNumber(int pc) {
    int[] info = myLineInfo;
    int length = info.length;
    if (length >= 2) {
      if (myLineInfoSorted) {
        // javac writes the table in start_pc order, so the last entry at or before pc is found by a
        // binary search. Duplicate start_pc entries keep the backward walk's answer: the last one.
        int low = 0;
        int high = length / 2 - 1;
        int found = -1;
        while (low <= high) {
          int middle = (low + high) >>> 1;
          if (info[middle * 2] <= pc) {
            found = middle;
            low = middle + 1;
          }
          else {
            high = middle - 1;
          }
        }
        if (found >= 0) {
          return info[found * 2 + 1];
        }
      }
      else {
        // Not sorted (not javac output, or a rewritten table): the original backward walk keeps the
        // "last entry whose start_pc is at or before pc" semantics for any order.
        for (int i = length - 2; i >= 0; i -= 2) {
          if (pc >= info[i]) {
            return info[i + 1];
          }
        }
      }
    }
    return -1;
  }

  public int[] getRawData() {
    return myLineInfo;
  }

  public void setLineInfo(int[] myLineInfo) {
    this.myLineInfo = myLineInfo;
    this.myLineInfoSorted = myLineInfo != null && isSortedByStartPc(myLineInfo);
  }

  private static boolean isSortedByStartPc(int[] info) {
    for (int i = 2; i < info.length; i += 2) {
      if (info[i - 2] > info[i]) {
        return false;
      }
    }
    return true;
  }
}