// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.attr;

import org.jetbrains.java.decompiler.code.BytecodeVersion;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

import java.io.IOException;
import java.util.*;
import java.util.stream.Stream;

/*
  u2 local_variable_table_length;
  local_variable {
    u2 start_pc;
    u2 length;
    u2 name_index;
    u2 descriptor_index;
    u2 index;
  }
*/
public class StructLocalVariableTableAttribute extends StructGeneralAttribute {
  private List<LocalVariable> localVariables = Collections.emptyList();
  private Map<Integer, Integer> indexVersion = new HashMap<>();
  // The table is read once and never mutated afterwards; queries index it by slot instead of
  // filtering every row. The fields are assigned once from a freshly built map, so a concurrent
  // first query may build it twice but both readers see a complete map.
  private volatile Map<Integer, List<LocalVariable>> rowsByIndex;
  private List<LocalVariable> variableList;

  @Override
  public void initContent(DataInputFullStream data, ConstantPool pool, BytecodeVersion version) throws IOException {
    int len = data.readUnsignedShort();
    if (len > 0) {
      localVariables = new ArrayList<>(len);
      indexVersion = new HashMap<>();
      rowsByIndex = null;
      variableList = null;

      for (int i = 0; i < len; i++) {
        int start_pc = data.readUnsignedShort();
        int length = data.readUnsignedShort();
        int nameIndex = data.readUnsignedShort();
        int descriptorIndex = data.readUnsignedShort();
        int varIndex = data.readUnsignedShort();
        localVariables.add(new LocalVariable(start_pc,
                                             length,
                                             pool.getPrimitiveConstant(nameIndex).getString(),
                                             pool.getPrimitiveConstant(descriptorIndex).getString(),
                                             varIndex));
      }
      for (int i = 0; i < localVariables.size(); i++) {
        localVariables.get(i).order = i;
      }
      Collections.sort(localVariables);
      versionVariables(localVariables);
    }
    else {
      localVariables = Collections.emptyList();
      rowsByIndex = null;
      variableList = null;
    }
  }

  public void add(StructLocalVariableTableAttribute attr) {
    localVariables.addAll(attr.localVariables);
    rowsByIndex = null;
    versionVariables(localVariables);
  }

  public String getName(int index, int visibleOffset) {
    return matchingVars(index, visibleOffset).map(v -> v.name).findFirst().orElse(null);
  }

  public String getDescriptor(int index, int visibleOffset) {
    return matchingVars(index, visibleOffset).map(v -> v.descriptor).findFirst().orElse(null);
  }

  public Stream<LocalVariable> matchingVars(int index, int visibleOffset) {
    return variablesAt(index).stream()
      .filter(v -> visibleOffset >= v.start_pc && visibleOffset < v.start_pc + v.length);
  }

  public Stream<LocalVariable> matchingVars(int index) {
    return variablesAt(index).stream();
  }

  /** The rows naming this slot, in table order. The returned list must not be modified. */
  public List<LocalVariable> variablesAt(int index) {
    List<LocalVariable> rows = rowsByIndex().get(index);
    return rows == null ? Collections.emptyList() : rows;
  }

  /** The first row naming this slot that opens at exactly this offset, or null. */
  public LocalVariable findAtStart(int index, int start) {
    for (LocalVariable row : variablesAt(index)) {
      if (row.start_pc == start) {
        return row;
      }
    }
    return null;
  }

  private Map<Integer, List<LocalVariable>> rowsByIndex() {
    Map<Integer, List<LocalVariable>> rows = this.rowsByIndex;
    if (rows == null) {
      rows = buildRowsByIndex();
    }
    return rows;
  }

  private synchronized Map<Integer, List<LocalVariable>> buildRowsByIndex() {
    Map<Integer, List<LocalVariable>> rows = this.rowsByIndex;
    if (rows != null) {
      return rows;
    }
    rows = new HashMap<>();
    for (LocalVariable variable : localVariables) {
      rows.computeIfAbsent(variable.index, key -> new ArrayList<>()).add(variable);
    }
    for (Map.Entry<Integer, List<LocalVariable>> entry : rows.entrySet()) {
      entry.setValue(Collections.unmodifiableList(entry.getValue()));
    }
    this.rowsByIndex = rows;
    return rows;
  }

  public Stream<LocalVariable> matchingVars(Statement stat) {
    BitSet values = new BitSet();
    stat.getOffset(values);
    return getRange(values.nextSetBit(0), values.length() - 1);
  }

  public Stream<LocalVariable> getRange(int start, int end) {
    return localVariables.stream().filter(v -> v.getStart() >= start && v.getEnd() <= end);
  }

  public boolean containsName(String name) {
    return localVariables.stream().anyMatch(v -> Objects.equals(v.name, name));
  }

  public Map<VarVersionPair, String> getMapNames() {
    Map<VarVersionPair, String> names = new HashMap<>();
    for (LocalVariable variable : localVariables) {
      names.put(variable.version, variable.name);
    }
    return names;
  }

  public Stream<LocalVariable> getVariables() {
    return localVariables.stream();
  }

  /** All rows in table order, without copying. The returned list must not be modified. */
  public List<LocalVariable> getVariableList() {
    List<LocalVariable> list = variableList;
    if (list == null) {
      list = Collections.unmodifiableList(localVariables);
      variableList = list;
    }
    return list;
  }

  /** The rows within a range, in table order, without streaming. The list must not be modified. */
  public List<LocalVariable> getRangeList(int start, int end) {
    if (start <= 0 && end == Integer.MAX_VALUE) {
      return getVariableList();
    }
    List<LocalVariable> result = new ArrayList<>();
    for (LocalVariable variable : localVariables) {
      if (variable.start_pc >= start && variable.start_pc + variable.length <= end) {
        result.add(variable);
      }
    }
    return Collections.unmodifiableList(result);
  }
  
  private void versionVariables(List<LocalVariable> vars) {
    for (LocalVariable var : vars) {
      Integer version = indexVersion.get(var.index);
      version = version == null ? 1 : version++;
      indexVersion.put(var.index, version);
      var.version = new VarVersionPair(var.index, version.intValue());
    }
  }

  public void mergeSignatures(StructLocalVariableTypeTableAttribute lvtt) {
      lvtt.backingAttribute.localVariables.stream().forEach(type -> localVariables.stream().filter(t -> t.compareTo(type) == 0).findFirst().ifPresent(lv -> lv.setSignature(type.descriptor)));
  }

  public static class LocalVariable implements Comparable<LocalVariable> {
    final int start_pc;
    final int length;
    final String name;
    final String descriptor;
    final int index;
    private String signature;
    // Both types are immutable, so one instance serves every caller.
    private VarType varType;
    private VarType signatureType;
    private VarVersionPair version;
    // Position in the attribute as read. javac writes entries when their scope closes, so a
    // variable emitted before the parameters was block scoped in the source.
    private int order = -1;

    public LocalVariable(int start_pc, int length, String name, String descriptor, int index) {
      this.start_pc = start_pc;
      this.length = length;
      this.name = name;
      this.descriptor = descriptor;
      this.index = index;
      this.version = new VarVersionPair(index, 0);
    }

    @Override
    public int compareTo(LocalVariable o) {
      if (this.index != o.index) return this.index - o.index;
      if (this.start_pc != o.start_pc) return this.start_pc - o.start_pc;
      return this.length - o.length;
    }
    
    public int getStartPC() {
      return start_pc;
    }

    public int getLength() {
      return length;
    }

    public int getIndex() {
      return index;
    }

    public String getName() {
      return name;
    }

    public String getDescriptor() {
      return descriptor;
    }

    public String getSignature() {
      return signature;
    }

    private void setSignature(String signature) {
      this.signature = signature;
      this.signatureType = null;
    }
    
    public int getStart() {
      return start_pc;
    }

    public int getEnd() {
      return start_pc + length;
    }

    public int getOrder() {
      return order;
    }

    public VarVersionPair getVersion() {
      return version;
    }

    public VarType getVarType() {
      VarType type = varType;
      if (type == null) {
        type = new VarType(descriptor);
        varType = type;
      }
      return type;
    }

    /**
     * The generic type recorded for this row, parsed once. A malformed signature throws exactly as
     * {@link GenericType#parse} does; callers keep their own fallback, and a failed parse caches
     * nothing so the next call retries with the same outcome.
     */
    public VarType getSignatureType() {
      VarType type = signatureType;
      if (type == null) {
        if (signature == null) {
          return null;
        }
        type = GenericType.parse(signature);
        signatureType = type;
      }
      return type;
    }
    
    @Override
    public String toString() {
      return "\'("+index+","+start_pc+'-'+getEnd()+")"+descriptor+(signature!=null ? "<"+signature+"> ":" ")+name+"\'";
    }

    public LocalVariable rename(String newName) {
      LocalVariable ret = new LocalVariable(start_pc, length, newName, descriptor, index);
      ret.signature = signature;
      ret.order = order;
      return ret;
    }
  }
}
