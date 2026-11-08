package org.jetbrains.java.decompiler.bench;

import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.extern.IResultSaver;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * In-process decompiler benchmark.
 *
 * <p>Each round constructs a fresh {@link Fernflower}, adds one version's classes directory as the
 * library and decompiles the scenario's classes into a discarding saver. The printed result is not
 * the point: the measured quantities are the bytes the thread allocated, the thread's CPU time,
 * the process's CPU time and the wall time. Allocation and CPU time are comparable across runs on
 * the same JVM and input; they do not depend on other processes or on the machine being otherwise
 * idle. Wall time is printed for context only.
 *
 * <p>Every version gets a library-only scenario and a sample of its whole class tree, so a change
 * cannot be tuned to one build or to a handful of named classes. The first usable version also
 * gets the named classes and a batch scenario for diagnosis.
 *
 * <p>Usage: {@code bench [--version V]... [--class NAME]... [--versions-dir DIR]
 * [--classes-dir DIR] [--sample N] [--warmup N] [--rounds N]}.
 */
public final class DecompilerBench {
  private static final String DEFAULT_VERSION = "1.21.11_unobfuscated";
  private static final List<String> DEFAULT_CLASSES = List.of(
    "net.minecraft.util.datafix.fixes.EquipmentFormatFix",
    "net.minecraft.client.data.models.BlockModelGenerators",
    "net.minecraft.client.Minecraft"
  );
  private static final String[] LAYER_NAMES = {"tiny", "small", "large", "huge"};

  private DecompilerBench() {
  }

  public static void main(String[] args) throws Exception {
    Map<String, String> options = parse(args);

    List<String> versions = new ArrayList<>();
    List<String> classNames = new ArrayList<>();
    for (Map.Entry<String, String> entry : options.entrySet()) {
      if (entry.getKey().matches("version\\d+")) {
        versions.add(entry.getValue());
      }
      else if (entry.getKey().matches("class\\d+")) {
        classNames.addAll(Arrays.asList(entry.getValue().split(",")));
      }
    }
    if (versions.isEmpty()) {
      versions.add(DEFAULT_VERSION);
    }
    if (classNames.isEmpty()) {
      classNames.addAll(DEFAULT_CLASSES);
    }

    int warmup = Integer.parseInt(options.getOrDefault("warmup", "1"));
    int rounds = Integer.parseInt(options.getOrDefault("rounds", "5"));
    int sampleSize = Integer.parseInt(options.getOrDefault("sample", "0"));
    boolean includeDiagnostics = !"0".equals(options.getOrDefault("diagnostics", "1"));
    File versionsDir = new File(options.getOrDefault("versions-dir", ".dev/cache/versions"));
    File classesOverride = options.containsKey("classes-dir")
      ? new File(options.get("classes-dir"))
      : null;

    System.err.printf(Locale.ROOT,
      "bench: java=%s os=%s cpus=%d versions=%s classes=%s warmup=%d rounds=%d sample=%d%n",
      System.getProperty("java.version"), System.getProperty("os.name"),
      Runtime.getRuntime().availableProcessors(), versions, classNames, warmup, rounds, sampleSize);

    List<Scenario> scenarios = new ArrayList<>();
    List<LayerReport> layerReports = new ArrayList<>();
    boolean diagnostics = includeDiagnostics;
    for (String version : versions) {
      File classesDir = classesOverride != null
        ? classesOverride
        : new File(versionsDir, version + "/classes");
      if (!classesDir.isDirectory()) {
        System.err.println("bench: skipping " + version + ", no classes directory at "
          + classesDir.getAbsolutePath());
        continue;
      }

      scenarios.add(new Scenario("library:" + version, List.of(), classesDir));

      if (diagnostics) {
        List<File> sources = new ArrayList<>();
        for (String className : classNames) {
          File source = new File(classesDir, className.replace('.', '/') + ".class");
          if (!source.isFile()) {
            System.err.println("bench: missing class file " + source.getAbsolutePath());
            System.exit(2);
          }
          sources.add(source);
        }
        for (int i = 0; i < classNames.size(); i++) {
          scenarios.add(new Scenario("single:" + version + ":" + simpleName(classNames.get(i)),
            List.of(sources.get(i)), classesDir));
        }
        scenarios.add(new Scenario("batch:" + version, sources, classesDir));
        diagnostics = false;
      }

      Sampling sampling = sample(classesDir, sampleSize);
      List<File> sampled = new ArrayList<>();
      Map<String, String> classLayer = new HashMap<>();
      for (Layer layer : sampling.layers()) {
        for (File file : layer.sample()) {
          sampled.add(file);
          classLayer.put(relativeName(classesDir, file), layer.name());
        }
      }
      if (!sampled.isEmpty()) {
        scenarios.add(new Scenario("sample:" + version, sampled, classesDir));
        layerReports.add(new LayerReport(version, sampling.layers(), classLayer));
      }
    }
    if (scenarios.isEmpty()) {
      System.err.println("bench: no usable version");
      System.exit(2);
    }

    Map<String, List<long[]>> results = new LinkedHashMap<>();
    Map<String, List<Map<String, Long>>> classTimings = new LinkedHashMap<>();
    for (Scenario scenario : scenarios) {
      results.put(scenario.name(), new ArrayList<>());
      if (scenario.name().startsWith("sample:")) {
        classTimings.put(scenario.name(), new ArrayList<>());
      }
    }
    for (int round = 0; round < warmup; round++) {
      for (Scenario scenario : scenarios) {
        decompile(scenario.sources(), scenario.library(), new HashMap<>());
      }
    }

    System.out.println("scenario\tround\tclasses\tallocatedBytes\tthreadCpuNanos\tprocessCpuNanos\twallNanos");
    for (int round = 0; round < rounds; round++) {
      for (Scenario scenario : scenarios) {
        Map<String, Long> timings = new HashMap<>();
        Measurement measurement = measure(scenario, timings);
        long[] metrics = measurement.metrics();
        results.get(scenario.name()).add(metrics);
        if (classTimings.containsKey(scenario.name())) {
          classTimings.get(scenario.name()).add(timings);
        }
        System.out.printf(Locale.ROOT, "%s\t%d\t%d\t%d\t%d\t%d\t%d%n",
          scenario.name(), round, scenario.sources().size(), metrics[0], metrics[1], metrics[2],
          metrics[3]);
      }
    }
    printSummary(results);
    printLayerShares(layerReports, classTimings);
  }

  private record Scenario(String name, List<File> sources, File library) {
  }

  private record Measurement(long[] metrics) {
  }

  private record LayerReport(String version, List<Layer> layers, Map<String, String> classLayer) {
  }

  private static Measurement measure(Scenario scenario, Map<String, Long> timings) {
    long allocated = allocatedBytes();
    long threadCpu = threadCpuNanos();
    long processCpu = processCpuNanos();
    long start = System.nanoTime();
    decompile(scenario.sources(), scenario.library(), timings);
    long wall = System.nanoTime() - start;
    long threadCpuEnd = threadCpuNanos();
    long processCpuEnd = processCpuNanos();
    long allocatedEnd = allocatedBytes();
    return new Measurement(new long[]{
      allocated < 0 || allocatedEnd < 0 ? -1 : allocatedEnd - allocated,
      threadCpu < 0 || threadCpuEnd < 0 ? -1 : threadCpuEnd - threadCpu,
      processCpu < 0 || processCpuEnd < 0 ? -1 : processCpuEnd - processCpu,
      wall});
  }

  private static void decompile(List<File> sources, File library, Map<String, Long> timings) {
    Map<String, Object> options = new HashMap<>(IFernflowerPreferences.getDefaults());
    Fernflower fernflower = new Fernflower(new DiscardSaver(), options, new TimingLogger(timings));
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

  private static long threadCpuNanos() {
    java.lang.management.ThreadMXBean thread = ManagementFactory.getThreadMXBean();
    return thread.isCurrentThreadCpuTimeSupported() ? thread.getCurrentThreadCpuTime() : -1;
  }

  private static long processCpuNanos() {
    return ProcessHandle.current().info().totalCpuDuration()
      .map(java.time.Duration::toNanos)
      .orElse(-1L);
  }

  private static Map<String, String> parse(String[] args) {
    Map<String, String> options = new LinkedHashMap<>();
    int classIndex = 0;
    int versionIndex = 0;
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      if (!arg.startsWith("--") || i + 1 >= args.length) {
        throw new IllegalArgumentException("usage: --version V --class NAME --versions-dir DIR "
          + "--classes-dir DIR --sample N --warmup N --rounds N");
      }
      String key = arg.substring(2);
      String value = args[++i];
      if (key.equals("class")) {
        key = "class" + classIndex++;
      }
      else if (key.equals("version")) {
        key = "version" + versionIndex++;
      }
      options.put(key, value);
    }
    return options;
  }

  private static String simpleName(String className) {
    return className.substring(className.lastIndexOf('.') + 1);
  }

  private static String relativeName(File classesDir, File classFile) {
    String root = classesDir.toPath().toAbsolutePath().normalize().toString();
    String path = classFile.toPath().toAbsolutePath().normalize().toString();
    String relative = path.startsWith(root) ? path.substring(root.length()) : classFile.getName();
    if (relative.startsWith(File.separator)) {
      relative = relative.substring(1);
    }
    relative = relative.replace(File.separatorChar, '/');
    return relative.endsWith(".class") ? relative.substring(0, relative.length() - 6) : relative;
  }

  private record Layer(String name, List<File> sample, long bytes) {
  }

  private record Sampling(List<Layer> layers) {
  }

  /**
   * A deterministic, size-stratified sample of the whole class tree. Classes are ordered by size
   * and cut into four layers; each layer's sample size is proportional to that layer's share of
   * the tree, so every layer is drawn at the same rate and the sample's cost estimates the whole
   * tree's. Inside a layer the sample is taken at even path intervals, so every package is
   * covered. Inner classes are included: a whole-tree decompile processes them too. The same tree
   * always yields the same sample.
   */
  private static Sampling sample(File classesDir, int size) throws IOException {
    if (size <= 0) {
      return new Sampling(List.of());
    }
    List<Path> classes = new ArrayList<>();
    Files.walkFileTree(classesDir.toPath(), new SimpleFileVisitor<>() {
      @Override
      public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
        if (file.getFileName().toString().endsWith(".class")) {
          classes.add(file);
        }
        return FileVisitResult.CONTINUE;
      }
    });
    classes.sort(Comparator.comparingLong((Path path) -> path.toFile().length())
      .thenComparing(Path::toString));
    int total = classes.size();
    int count = Math.min(size, total);
    int layers = LAYER_NAMES.length;
    int[] start = new int[layers];
    int[] layerSize = new int[layers];
    for (int layer = 0; layer < layers; layer++) {
      start[layer] = (int) ((long) total * layer / layers);
      layerSize[layer] = (int) ((long) total * (layer + 1) / layers) - start[layer];
    }
    int[] allocated = new int[layers];
    double[] remainders = new double[layers];
    int assigned = 0;
    for (int layer = 0; layer < layers; layer++) {
      double exact = total == 0 ? 0 : (double) count * layerSize[layer] / total;
      allocated[layer] = Math.min((int) exact, layerSize[layer]);
      remainders[layer] = exact - (int) exact;
      assigned += allocated[layer];
    }
    while (assigned < count) {
      int best = -1;
      for (int layer = 0; layer < layers; layer++) {
        if (allocated[layer] < layerSize[layer]
          && (best < 0 || remainders[layer] > remainders[best])) {
          best = layer;
        }
      }
      if (best < 0) {
        break;
      }
      allocated[best]++;
      remainders[best] -= 1.0;
      assigned++;
    }

    List<Layer> result = new ArrayList<>();
    for (int layer = 0; layer < layers; layer++) {
      if (allocated[layer] == 0) {
        continue;
      }
      List<Path> slice = new ArrayList<>(classes.subList(start[layer], start[layer] + layerSize[layer]));
      slice.sort(Comparator.comparing(Path::toString));
      List<File> picked = new ArrayList<>(allocated[layer]);
      for (int i = 0; i < allocated[layer]; i++) {
        picked.add(slice.get((int) ((long) i * slice.size() / allocated[layer])).toFile());
      }
      long bytes = picked.stream().mapToLong(File::length).sum();
      result.add(new Layer(LAYER_NAMES[layer], picked, bytes));
    }
    return new Sampling(result);
  }

  private static void printSummary(Map<String, List<long[]>> results) {
    System.out.println("summary\tscenario\trounds\tallocatedBytesMedian\tallocatedBytesMad\tthreadCpuNanosMedian\tthreadCpuNanosMad\tprocessCpuNanosMedian\tprocessCpuNanosMad\twallNanosMedian\twallNanosMad");
    for (Map.Entry<String, List<long[]>> entry : results.entrySet()) {
      List<Long> allocated = column(entry.getValue(), 0);
      List<Long> threadCpu = column(entry.getValue(), 1);
      List<Long> processCpu = column(entry.getValue(), 2);
      List<Long> wall = column(entry.getValue(), 3);
      System.out.printf(Locale.ROOT, "summary\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d%n",
        entry.getKey(), entry.getValue().size(),
        median(allocated), mad(allocated),
        median(threadCpu), mad(threadCpu),
        median(processCpu), mad(processCpu),
        median(wall), mad(wall));
    }
  }

  private static void printLayerShares(List<LayerReport> reports,
                                       Map<String, List<Map<String, Long>>> classTimings) {
    System.out.println("layers\tversion\tlayer\tclasses\tbytes\tclassNanosMedian\tsharePercent");
    for (LayerReport report : reports) {
      List<Map<String, Long>> rounds = classTimings.getOrDefault("sample:" + report.version(),
        List.of());
      Map<String, List<Long>> layerTimes = new LinkedHashMap<>();
      for (Layer layer : report.layers()) {
        List<Long> times = new ArrayList<>();
        for (Map<String, Long> round : rounds) {
          long sum = 0;
          for (Map.Entry<String, String> entry : report.classLayer().entrySet()) {
            if (entry.getValue().equals(layer.name())) {
              sum += round.getOrDefault(entry.getKey(), 0L);
            }
          }
          times.add(sum);
        }
        layerTimes.put(layer.name(), times);
      }
      long total = 0;
      Map<String, Long> medians = new LinkedHashMap<>();
      for (Layer layer : report.layers()) {
        long median = median(layerTimes.get(layer.name()));
        medians.put(layer.name(), median);
        if (median > 0) {
          total += median;
        }
      }
      for (Layer layer : report.layers()) {
        long median = medians.get(layer.name());
        double share = median > 0 && total > 0 ? median * 100.0 / total : -1;
        System.out.printf(Locale.ROOT, "layers\t%s\t%s\t%d\t%d\t%d\t%.2f%n",
          report.version(), layer.name(), layer.sample().size(), layer.bytes(), median, share);
      }
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

  /** Attributes the decompiler thread's time to the class being printed, without extra passes. */
  private static final class TimingLogger extends IFernflowerLogger {
    private final Map<String, Long> timings;
    private String current;
    private long started;

    TimingLogger(Map<String, Long> timings) {
      this.timings = timings;
    }

    @Override
    public void writeMessage(String message, Severity severity) {
    }

    @Override
    public void writeMessage(String message, Severity severity, Throwable t) {
    }

    @Override
    public void startClass(String className) {
      current = className;
      started = System.nanoTime();
    }

    @Override
    public void endClass() {
      if (current != null) {
        timings.merge(current, System.nanoTime() - started, Long::sum);
        current = null;
      }
    }
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
