package org.jetbrains.java.decompiler.bench;

import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.extern.IResultSaver;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * In-process decompiler benchmark.
 *
 * <p>Each round constructs a fresh {@link Fernflower}, adds the classes directory as the library
 * and decompiles the scenario's classes into a discarding saver. The printed result is not the
 * point: the measured quantities are the bytes the thread allocated, its CPU time and the wall
 * time. Allocation and CPU time are comparable across runs on the same JVM and input; they do not
 * depend on other processes or on the machine being otherwise idle. Wall time is printed for
 * context only.
 *
 * <p>Usage: {@code bench [--version V] [--classes-dir DIR] [--class NAME]... [--warmup N]
 * [--rounds N]}. Defaults: 1.21.11_unobfuscated, .dev/cache/versions/&lt;version&gt;/classes, three
 * representative classes (small, large expression printer, very large class), one warmup round,
 * five measured rounds, plus a batch scenario that decompiles all of them in one context.
 */
public final class DecompilerBench {
  private static final String DEFAULT_VERSION = "1.21.11_unobfuscated";
  private static final List<String> DEFAULT_CLASSES = List.of(
    "net.minecraft.util.datafix.fixes.EquipmentFormatFix",
    "net.minecraft.client.data.models.BlockModelGenerators",
    "net.minecraft.client.Minecraft"
  );

  private DecompilerBench() {
  }

  public static void main(String[] args) throws Exception {
    Map<String, String> options = parse(args);
    String version = options.getOrDefault("version", DEFAULT_VERSION);
    File classesDir = new File(options.getOrDefault("classes-dir",
      ".dev/cache/versions/" + version + "/classes"));
    if (!classesDir.isDirectory()) {
      System.err.println("bench: no classes directory at " + classesDir.getAbsolutePath());
      System.exit(2);
    }

    List<String> classNames = new ArrayList<>();
    for (Map.Entry<String, String> entry : options.entrySet()) {
      if (entry.getKey().matches("class\\d+")) {
        classNames.addAll(Arrays.asList(entry.getValue().split(",")));
      }
    }
    if (classNames.isEmpty()) {
      classNames.addAll(DEFAULT_CLASSES);
    }

    int warmup = Integer.parseInt(options.getOrDefault("warmup", "1"));
    int rounds = Integer.parseInt(options.getOrDefault("rounds", "5"));

    System.err.printf(Locale.ROOT, "bench: java=%s os=%s cpus=%d version=%s classes=%s warmup=%d rounds=%d%n",
      System.getProperty("java.version"), System.getProperty("os.name"),
      Runtime.getRuntime().availableProcessors(), version, classNames, warmup, rounds);

    List<File> sources = new ArrayList<>();
    for (String className : classNames) {
      File source = new File(classesDir, className.replace('.', '/') + ".class");
      if (!source.isFile()) {
        System.err.println("bench: missing class file " + source.getAbsolutePath());
        System.exit(2);
      }
      sources.add(source);
    }

    List<Scenario> scenarios = new ArrayList<>();
    scenarios.add(new Scenario("library", List.of()));
    for (int i = 0; i < classNames.size(); i++) {
      scenarios.add(new Scenario("single:" + simpleName(classNames.get(i)), List.of(sources.get(i))));
    }
    scenarios.add(new Scenario("batch", sources));

    Map<String, List<long[]>> results = new LinkedHashMap<>();
    for (Scenario scenario : scenarios) {
      results.put(scenario.name(), new ArrayList<>());
    }
    for (int round = 0; round < warmup; round++) {
      for (Scenario scenario : scenarios) {
        decompile(scenario.sources(), classesDir);
      }
    }

    System.out.println("scenario\tround\tclasses\tallocatedBytes\tcpuNanos\twallNanos");
    for (int round = 0; round < rounds; round++) {
      for (Scenario scenario : scenarios) {
        long[] metrics = measure(scenario.sources(), classesDir);
        results.get(scenario.name()).add(metrics);
        System.out.printf(Locale.ROOT, "%s\t%d\t%d\t%d\t%d\t%d%n",
          scenario.name(), round, scenario.sources().size(), metrics[0], metrics[1], metrics[2]);
      }
    }
    printSummary(results);
  }

  private record Scenario(String name, List<File> sources) {
  }

  private static long[] measure(List<File> sources, File library) {
    long allocated = allocatedBytes();
    long cpu = cpuNanos();
    long start = System.nanoTime();
    decompile(sources, library);
    long wall = System.nanoTime() - start;
    long cpuEnd = cpuNanos();
    long allocatedEnd = allocatedBytes();
    return new long[]{
      allocated < 0 || allocatedEnd < 0 ? -1 : allocatedEnd - allocated,
      cpu < 0 || cpuEnd < 0 ? -1 : cpuEnd - cpu,
      wall};
  }

  private static void printSummary(Map<String, List<long[]>> results) {
    System.out.println("summary\tscenario\trounds\tallocatedBytesMedian\tallocatedBytesMad\tcpuNanosMedian\tcpuNanosMad\twallNanosMedian\twallNanosMad");
    for (Map.Entry<String, List<long[]>> entry : results.entrySet()) {
      List<Long> allocated = column(entry.getValue(), 0);
      List<Long> cpu = column(entry.getValue(), 1);
      List<Long> wall = column(entry.getValue(), 2);
      System.out.printf(Locale.ROOT, "summary\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d%n",
        entry.getKey(), entry.getValue().size(),
        median(allocated), mad(allocated), median(cpu), mad(cpu), median(wall), mad(wall));
    }
  }

  private static List<Long> column(List<long[]> rows, int index) {
    List<Long> values = new ArrayList<>();
    for (long[] row : rows) {
      if (row[index] >= 0) {
        values.add(row[index]);
      }
    }
    return values;
  }

  private static long median(List<Long> values) {
    if (values.isEmpty()) {
      return -1;
    }
    List<Long> sorted = new ArrayList<>(values);
    sorted.sort(Long::compare);
    int middle = sorted.size() / 2;
    return sorted.size() % 2 == 0
      ? (sorted.get(middle - 1) + sorted.get(middle)) / 2
      : sorted.get(middle);
  }

  private static long mad(List<Long> values) {
    long median = median(values);
    if (median < 0) {
      return -1;
    }
    List<Long> deviations = new ArrayList<>();
    for (long value : values) {
      deviations.add(Math.abs(value - median));
    }
    return median(deviations);
  }

  private static void decompile(List<File> sources, File library) {
    Map<String, Object> options = new HashMap<>(IFernflowerPreferences.getDefaults());
    Fernflower fernflower = new Fernflower(new DiscardSaver(), options, IFernflowerLogger.NO_OP);
    fernflower.addLibrary(library);
    for (File source : sources) {
      fernflower.addSource(source);
    }
    fernflower.decompileContext();
  }

  private static long allocatedBytes() {
    try {
      java.lang.management.ThreadMXBean thread = ManagementFactory.getThreadMXBean();
      if (thread instanceof com.sun.management.ThreadMXBean hotSpot) {
        return hotSpot.getCurrentThreadAllocatedBytes();
      }
    }
    catch (Throwable ignored) {
      // Not a HotSpot thread bean; allocation bytes are unavailable.
    }
    return -1;
  }

  private static long cpuNanos() {
    java.lang.management.ThreadMXBean thread = ManagementFactory.getThreadMXBean();
    return thread.isCurrentThreadCpuTimeSupported() ? thread.getCurrentThreadCpuTime() : -1;
  }

  private static Map<String, String> parse(String[] args) {
    Map<String, String> options = new LinkedHashMap<>();
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      if (!arg.startsWith("--") || i + 1 >= args.length) {
        throw new IllegalArgumentException("usage: --version V --classes-dir DIR --class NAME "
          + "--warmup N --rounds N");
      }
      String key = arg.substring(2);
      String value = args[++i];
      if (key.equals("class")) {
        options.merge("class" + options.size(), value, (first, second) -> first + "," + second);
      }
      else {
        options.put(key, value);
      }
    }
    return options;
  }

  private static String simpleName(String className) {
    return className.substring(className.lastIndexOf('.') + 1);
  }

  private static final class DiscardSaver implements IResultSaver {
    @Override
    public void saveFolder(String path) {
    }

    @Override
    public void copyFile(String source, String path, String entryName) {
    }

    @Override
    public void copyEntry(String source, String path, String archiveName, String entry) {
    }

    @Override
    public void saveClassFile(String path, String qualifiedName, String entryName, String content,
                              int[] mapping) {
    }

    @Override
    public void createArchive(String path, String archiveName, java.util.jar.Manifest manifest) {
    }

    @Override
    public void saveDirEntry(String path, String archiveName, String entryName) {
    }

    @Override
    public void saveClassEntry(String path, String archiveName, String qualifiedName,
                               String entryName, String content) {
    }

    @Override
    public void closeArchive(String path, String archiveName) {
    }

    @Override
    public void close() throws IOException {
    }
  }
}
