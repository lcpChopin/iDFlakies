package edu.illinois.cs.dt.tools.plugin;

import com.google.common.base.Preconditions;
import edu.illinois.cs.dt.tools.detection.detectors.Detector;
import edu.illinois.cs.dt.tools.detection.detectors.DetectorFactory;
import edu.illinois.cs.dt.tools.utility.ErrorLogger;
import edu.illinois.cs.dt.tools.utility.Level;
import edu.illinois.cs.dt.tools.utility.Logger;
import edu.illinois.cs.dt.tools.utility.PathManager;
import edu.illinois.cs.testrunner.configuration.Configuration;
import edu.illinois.cs.testrunner.data.framework.TestFramework;
import edu.illinois.starts.asm.ClassReader;
import edu.illinois.starts.helpers.Writer;
import edu.illinois.starts.util.Pair;

import org.apache.commons.codec.binary.Hex;
import org.apache.commons.collections.map.HashedMap;
import org.apache.maven.artifact.DependencyResolutionRequiredException;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.ResolutionScope;
import org.apache.maven.project.MavenProject;
import org.apache.maven.surefire.booter.Classpath;
import org.apache.maven.surefire.booter.SurefireExecutionException;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;

import com.microsoft.z3.*;

// import org.sosy_lab.java_smt.SolverContextFactory;
// import org.sosy_lab.java_smt.api.SolverContext;

import static edu.illinois.starts.helpers.ZLCHelper.STAR_FILE;

@Mojo(name = "incdetect", defaultPhase = LifecyclePhase.TEST, requiresDependencyResolution = ResolutionScope.TEST)
public class IncDetectorMojo extends DetectorMojo {

    protected static String CLASSES = "classes";
    protected static String EQUAL = "=";
    protected static String JAR_CHECKSUMS = "jar-checksums";
    protected static String SF_CLASSPATH = "sf-classpath";
    protected static String TEST_CLASSES = "test-classes";
    private static final String TARGET = "target";

    /**
     * The directory in which to store STARTS artifacts that are needed between runs.
     */
    protected String artifactsDir;

    protected String RTSDir;

    protected ClassLoader loader;

    protected List<Pair> jarCheckSums = null;

    protected Set<String> selectedTests;

    // the dependency map from test classes to their dependencies (classes)
    protected Map<String, Set<String>> transitiveClosure;

    // the dependency map from classes to their dependencies (test classes)
    protected Map<String, Set<String>> reverseTransitiveClosure;

    private Classpath sureFireClassPath;

    protected boolean selectMore;

    protected boolean detectOrNot;

    protected boolean selectAll;

    protected Path ekstaziSelectedTestsPath;

    protected Path startsSelectedTestsPath;

    protected Path startsDependenciesPath;

    protected boolean isEkstazi;

    private Set<String> affectedTestClasses;

    private static Set<String> immutableList;

    private List<String> allTestClasses;

    private List<String> allTestMethods;

    private List<String> finalSelectedTests;

    private Set<Pair> pairSet;

    private Set<Pair> crossClassPairSet;

    private Set<Pair> classesPairSet;

    private static int[][] r;

    private List<List<String>> orders;

    protected String pairsFile;

    protected Map<String, Set<String>> fieldsToTests;

    protected Map<String, Set<String>> testsToFields;

    @Override
    public void execute() {
        superExecute();

        final ErrorLogger logger = new ErrorLogger();
        this.outputPath = PathManager.detectionResults();
        this.coordinates = mavenProject.getGroupId() + ":" + mavenProject.getArtifactId() + ":" + mavenProject.getVersion();

        try {
            defineSettings(logger, mavenProject);
            loadTestRunners(logger, mavenProject);
        } catch (IOException e) {
            e.printStackTrace();
        }
        if (this.runner == null) {
            return;
        }

        try {
            allTestClasses = getTestClasses(mavenProject, this.runner.framework());
            finalSelectedTests = getTests(mavenProject, this.runner.framework());
            storeOrdersByAsm();
            writeNumOfOrders(orders, artifactsDir);
        } catch (IOException e) {
            e.printStackTrace();
        }

        long startTime = System.currentTimeMillis();
        logger.runAndLogError(() -> detectorExecute(logger, mavenProject, moduleRounds(coordinates)));
        timing(startTime);
    }

    // specilized for Tuscan
    protected Void detectorExecute(final ErrorLogger logger, final MavenProject mavenProject, final int rounds) throws IOException {
        final List<String> tests = getTests(mavenProject, this.runner.framework());

        if (!tests.isEmpty()) {
            Files.createDirectories(outputPath);
            Files.write(PathManager.originalOrderPath(), String.join(System.lineSeparator(), getOriginalOrder(mavenProject, this.runner.framework(), true)).getBytes());
            Files.write(PathManager.selectedTestPath(), String.join(System.lineSeparator(), tests).getBytes());
            final Detector detector;
            if (DetectorFactory.detectorType().equals("tuscan")){
                System.out.println("TUSCAN LA!!!");
                int newRounds = rounds;
                if (rounds > orders.size()) {
                    newRounds = orders.size();
                }
                detector = DetectorFactory.makeDetector(this.runner, mavenProject.getBasedir(), tests, newRounds, orders);
            } else {
                detector = DetectorFactory.makeDetector(this.runner, mavenProject.getBasedir(), tests, rounds);
            }
            Logger.getGlobal().log(Level.INFO, "Created dependent test detector (" + detector.getClass() + ").");
            detector.writeTo(outputPath);
        } else {
            String errorMsg = "Module has no tests, not running detector.";
            Logger.getGlobal().log(Level.INFO, errorMsg);
            logger.writeError(errorMsg);
        }

        return null;
    }

    private void getPairs() {
        Path path = relativePath(PathManager.modulePath(), Paths.get(pairsFile));
        try {
            Set<String> fieldsList = new HashSet<>();
            Set<String> leftFieldsList = new HashSet<>();
            BufferedReader in = Files.newBufferedReader(path, StandardCharsets.UTF_8);
            String str;
            while ((str = in.readLine()) != null) {
                // System.out.println(str);
                String test = str.substring(0, str.indexOf(','));
                String field = str.substring(str.indexOf(',') + 1);
                Set<String> fieldsSet = new HashSet<>();
                if (testsToFields.keySet().contains(test)) {
                    fieldsSet = testsToFields.get(test);
                }
                String className = field.substring(0, field.lastIndexOf('.'));
                String fieldName = field.substring(field.lastIndexOf('.') + 1);
                if(fieldsList.contains(field)) {
                    if (leftFieldsList.contains(field)) {
                        fieldsSet.add(field);
                        testsToFields.put(test, fieldsSet);
                    }
                }
                else {
                    fieldsList.add(field);
                    try {
                        Class clazz = loader.loadClass(className);
                        Field field1 = clazz.getDeclaredField(fieldName);
                        if (!isImmutable(field1)) {
                            // System.out.println("TEST: " + test + "; " + field);
                            fieldsSet.add(field);
                            testsToFields.put(test, fieldsSet);
                            leftFieldsList.add(field);
                        }
                    } catch (ClassNotFoundException e) {
                        e.printStackTrace();
                    } catch (NoSuchFieldException e) {
                        e.printStackTrace();
                    }
                }
            }
            fieldsToTests = getReverseClosure(testsToFields);
        } catch (IOException e) {
            e.printStackTrace();
        }
        for (String key: fieldsToTests.keySet()) {
            Set<String> testsSet = fieldsToTests.get(key);
            List<String> testsList = new LinkedList<>();
            for (String testItem : testsSet) {
                testsList.add(testItem);
            }
            for (int i = 0; i < testsSet.size() - 1; i++) {
                for (int j = 0; j < testsSet.size() - 1; j++) {
                    String clzName0 = testsList.get(i).substring(0, testsList.get(i).lastIndexOf('.'));
                    String clzName1 = testsList.get(j).substring(0, testsList.get(j).lastIndexOf('.'));
                    if (!clzName0.equals(clzName1)) {
                        crossClassPairSet.add(new Pair<>(testsList.get(i), testsList.get(j)));
                        crossClassPairSet.add(new Pair<>(testsList.get(j), testsList.get(i)));
                    } else {
                        pairSet.add(new Pair<>(testsList.get(i), testsList.get(j)));
                        pairSet.add(new Pair<>(testsList.get(j), testsList.get(i)));
                    }
                }
            }
        }
    }

    private void storeOrdersByAsm() {
        orders = new LinkedList<>();

        int clazzSize = allTestClasses.size();
        int testsSize = finalSelectedTests.size();
        Set<Pair> remainingPairs = new HashSet<>(pairSet);

        Map<String, List<String>> occurrenceMap = new HashedMap();
        for (Pair pairItem : remainingPairs) {
            List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
            valueList.add((String) pairItem.getValue());
            occurrenceMap.put((String) pairItem.getKey(), valueList);
            List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
            keyList.add((String) pairItem.getKey());
            occurrenceMap.put((String) pairItem.getValue(), keyList);
        }
        List<Map.Entry<String, List<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
        // descending order
        Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

        Set<Pair> remainingCrossClassPairs = new HashSet<>(crossClassPairSet);
        while (!remainingCrossClassPairs.isEmpty()) {
            List<String> order = new LinkedList<>();
            List<String> sequence = new LinkedList<>();
            String lastLeftAddedTest = "";
            String lastRightAddedTest = "";
            Set<String> processedClasses = new HashSet<>();
            int leftIndex = 0;
            int rightIndex = 0;
            System.out.println("CrossPairsSize: " + remainingCrossClassPairs.size());
            System.out.println("CLAZZSIZE: " + clazzSize);
            while(order.size() != clazzSize) {
                Pair pair1 = getPairs(sequence, lastLeftAddedTest, remainingCrossClassPairs, processedClasses, true);
                if (!pair1.toString().equals("=")) {
                    remainingCrossClassPairs.remove(pair1);
                    if (sequence.contains(lastLeftAddedTest)) {
                        leftIndex = sequence.indexOf(lastLeftAddedTest);
                    }
                    if (sequence.contains(lastRightAddedTest)) {
                        rightIndex = sequence.indexOf(lastRightAddedTest);
                    }
                    lastLeftAddedTest = pair1.getKey().toString();
                    String test2 = pair1.getValue().toString();
                    sequence.add(leftIndex, test2);
                    sequence.add(leftIndex, lastLeftAddedTest);
                    if (rightIndex < sequence.indexOf(test2)) {
                        lastRightAddedTest = test2;
                        rightIndex = sequence.indexOf(test2);
                    }
                    String c1 = lastLeftAddedTest.substring(0, lastLeftAddedTest.lastIndexOf('.'));
                    String c2 = test2.substring(0, test2.lastIndexOf('.'));
                    processedClasses.add(c1);
                    processedClasses.add(c2);
                    System.out.println("PAIR1: " + pair1.toString());
                }
                Pair pair2 = getPairs(sequence, lastRightAddedTest, remainingCrossClassPairs, processedClasses, false);
                if (!pair2.toString().equals("=")) {
                    remainingCrossClassPairs.remove(pair2);
                    if (sequence.contains(lastRightAddedTest)) {
                        rightIndex = sequence.indexOf(lastRightAddedTest);
                    }
                    String test1 = pair2.getKey().toString();
                    lastRightAddedTest = pair2.getValue().toString();
                    sequence.add(rightIndex + 1, test1);
                    sequence.add(rightIndex + 2, lastRightAddedTest);
                    if (leftIndex > sequence.indexOf(test1)) {
                        lastLeftAddedTest = test1;
                        leftIndex = sequence.indexOf(test1);
                    }
                    String c1 = test1.substring(0, test1.lastIndexOf('.'));
                    String c2 = lastRightAddedTest.substring(0, lastRightAddedTest.lastIndexOf('.'));
                    processedClasses.add(c1);
                    processedClasses.add(c2);
                    System.out.println("PAIR2: " + pair2.toString());
                }
                // System.out.println("ORDER: " + sequence.toString());
                if (pair1.toString().equals("=") && pair2.toString().equals("=")) {
                    order.addAll(sequence);
                    sequence = new LinkedList<>();
                    lastLeftAddedTest = "";
                    lastRightAddedTest = "";
                    leftIndex = 0;
                    rightIndex = 0;
                }
            }
            System.out.println("ORDER: " + order);
            System.exit(1);
        }
    }

    protected Pair getPairs(List<String> sequence, String lastAddedTest, Set<Pair> remainingPairs, Set<String> processedClasses, boolean left) {
        Map<String, List<String>> occurrenceMap = new HashMap();
        for (Pair pairItem : remainingPairs) {
            List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
            valueList.add((String) pairItem.getValue());
            occurrenceMap.put((String) pairItem.getKey(), valueList);
            List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
            keyList.add((String) pairItem.getKey());
            occurrenceMap.put((String) pairItem.getValue(), keyList);
        }
        List<Map.Entry<String, List<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
        // descending sequence
        Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

        String testClass = "";
        if (!lastAddedTest.equals("")) {
            testClass = lastAddedTest.substring(0, lastAddedTest.lastIndexOf('.'));
        }
        if (left) {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String firstTest = occurrenceSortedList.get(i).getKey();
                String firstTestClass = firstTest.substring(0, firstTest.lastIndexOf('.'));
                if (!sequence.contains(firstTest) && (firstTestClass.equals(testClass) || (lastAddedTest.equals("") && !processedClasses.contains(firstTestClass)))) {
                    for (String item : occurrenceSortedList.get(i).getValue()) {
                        String itemClass = item.substring(0, item.lastIndexOf('.'));
                        if (!sequence.contains(item) && !processedClasses.contains(itemClass)) {
                            Pair pair = new Pair<>(item, firstTest);
                            return pair;
                        }
                    }
                }
            }
            // release restriction
            
        } else {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String firstTest = occurrenceSortedList.get(i).getKey();
                String firstTestClass = firstTest.substring(0, firstTest.lastIndexOf('.'));
                if (!sequence.contains(firstTest) && (firstTestClass.equals(testClass) || (lastAddedTest.equals("") && !processedClasses.contains(firstTestClass)))) {
                    for (String item : occurrenceSortedList.get(i).getValue()) {
                        String itemClass = item.substring(0, item.lastIndexOf('.'));
                        if (!sequence.contains(item) && !processedClasses.contains(itemClass)) {
                            Pair pair = new Pair<>(firstTest, item);
                            return pair;
                        }
                    }
                }
            }
        }
        return new Pair<>("", "");
    }

    protected String getItem(List<String> order, String test, Set<Pair> remainingPairs, boolean left) {
        Map<String, List<String>> occurrenceMap = new HashedMap();
        for (Pair pairItem : remainingPairs) {
            List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
            valueList.add((String) pairItem.getValue());
            occurrenceMap.put((String) pairItem.getKey(), valueList);
            List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
            keyList.add((String) pairItem.getKey());
            occurrenceMap.put((String) pairItem.getValue(), keyList);
        }
        List<Map.Entry<String, List<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
        // descending order
        Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

        if (order.isEmpty() && test.equals("")) {
            return occurrenceSortedList.get(0).getKey();
        }

        if (left) {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String potentialTest = occurrenceSortedList.get(i).getKey();
                Pair testPair = new Pair<>(potentialTest, test);
                if (remainingPairs.contains(testPair) && !order.contains(potentialTest)) {
                    return potentialTest;
                }
            }
        } else {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String potentialTest = occurrenceSortedList.get(i).getKey();
                Pair testPair = new Pair<>(test, potentialTest);
                if (remainingPairs.contains(testPair) && !order.contains(potentialTest)) {
                    return potentialTest;
                }
            }
        }
        return "";
    }

    private ClassLoader createClassLoader(Classpath sfClassPath) {
        long start = System.currentTimeMillis();
        ClassLoader loader = null;
        try {
            loader = sfClassPath.createClassLoader(false, false, "MyRole");
        } catch (SurefireExecutionException see) {
            see.printStackTrace();
        }
        long end = System.currentTimeMillis();
        Logger.getGlobal().log(Level.FINE, "[PROFILE] IncDetectorPlugin(createClassLoader): "
                + Writer.millsToSeconds(end - start));
        return loader;
    }

    public Path relativePath(final Path initial, final Path relative) {
        Preconditions.checkState(!relative.isAbsolute(),
                "PathManager.path(): Cache paths must be relative, not absolute (%s)", relative);

        return initial.resolve(relative);
    }

    @Override
    protected void defineSettings(final ErrorLogger logger, final MavenProject project) throws IOException {
        super.defineSettings(logger, project);

        pairsFile = Configuration.config().getProperty("dt.asm.pairsfile", "");

        artifactsDir = getArtifactsDir();
        testsToFields = new HashMap();
        fieldsToTests = new HashMap();

        pairSet = new HashSet<>();
        crossClassPairSet = new HashSet<>();

        getImmutableList();

        getSureFireClassPath(project);
        loader = createClassLoader(sureFireClassPath);
        getPairs();
    }

    private String getArtifactsDir() throws FileNotFoundException {
        if (artifactsDir == null) {
            artifactsDir = PathManager.cachePath().toString();
            File file = new File(artifactsDir);
            if (!file.mkdirs() && !file.exists()) {
                throw new FileNotFoundException("I could not create artifacts dir: " + artifactsDir);
            }
        }
        return artifactsDir;
    }

    private Map<String, Set<String>> getReverseClosure(Map<String, Set<String>> transitiveClosure) {
        Map<String, Set<String>> reverseTransitiveClosure = new HashMap<>();
        for (Map.Entry<String, Set<String>> entry : transitiveClosure.entrySet()) {
            for (String dep : entry.getValue()) {
                Set<String> reverseDeps = new HashSet<>();
                if (reverseTransitiveClosure.containsKey(dep)) {
                    reverseDeps = reverseTransitiveClosure.get(dep);
                    reverseDeps.add(entry.getKey());
                    reverseTransitiveClosure.replace(dep, reverseDeps);
                }
                else {
                    reverseDeps.add(entry.getKey());
                    reverseTransitiveClosure.putIfAbsent(dep, reverseDeps);
                }
            }
        }
        return reverseTransitiveClosure;
    }

    private Classpath getSureFireClassPath(final MavenProject project) {
        long start = System.currentTimeMillis();
        if (sureFireClassPath == null) {
            try {
                sureFireClassPath = new Classpath(project.getTestClasspathElements());
            } catch (DependencyResolutionRequiredException e) {
                e.printStackTrace();
            }
        }
        Logger.getGlobal().log(Level.FINEST, "SF-CLASSPATH: " + sureFireClassPath.getClassPath());
        long end = System.currentTimeMillis();
        Logger.getGlobal().log(Level.FINE, "[PROFILE] IncDetectorPlugin(getSureFireClassPath): "
                + Writer.millsToSeconds(end - start));
        return sureFireClassPath;
    }

    private List<String> getTestClasses(
            final MavenProject project,
            TestFramework testFramework) throws IOException {
        List<String> tests = getOriginalOrder(project, testFramework, true);

        String delimiter = testFramework.getDelimiter();
        List<String> classes = new ArrayList<>();
        for (String test : tests){
            String clazz = test.substring(0, test.lastIndexOf(delimiter));
            if (!classes.contains(clazz)) {
                classes.add(clazz);
            }
        }

        return classes;
    }

    /**
     * Compute the checksum for the given map and return the jar
     * and the checksum as a string.
     *
     * @param jar  The jar whose checksum we need to compute.
     */
    private Pair<String, String> getJarToChecksumMapping(String jar) {
        Pair<String, String> pair = new Pair<>(jar, "-1");
        byte[] bytes;
        int bufSize = 65536 * 2;
        try {
            MessageDigest md = MessageDigest.getInstance("MD5");
            InputStream is = Files.newInputStream(Paths.get(jar));
            bytes = new byte[bufSize];
            int size = is.read(bytes, 0, bufSize);
            while (size >= 0) {
                md.update(bytes, 0, size);
                size = is.read(bytes, 0, bufSize);
            }
            pair = new Pair<>(jar, Hex.encodeHexString(md.digest()));
        } catch (IOException | NoSuchAlgorithmException e) {
            e.printStackTrace();
        }
        return pair;
    }

    private void getImmutableList() {
        if (immutableList == null) {
            immutableList = new HashSet<>();

            immutableList.add("java.lang.String");
            immutableList.add("java.lang.Enum");
            immutableList.add("java.lang.StackTraceElement");
            immutableList.add("java.math.BigInteger");
            immutableList.add("java.math.BigDecimal");
            immutableList.add("java.io.File");
            immutableList.add("java.awt.Font");
            immutableList.add("java.awt.BasicStroke");
            immutableList.add("java.awt.Color");
            immutableList.add("java.awt.GradientPaint");
            immutableList.add("java.awt.LinearGradientPaint");
            immutableList.add("java.awt.RadialGradientPaint");
            immutableList.add("java.awt.Cursor");
            immutableList.add("java.util.Locale");
            immutableList.add("java.util.UUID");
            immutableList.add("java.util.Collections");
            immutableList.add("java.net.URL");
            immutableList.add("java.net.URI");
            immutableList.add("java.net.Inet4Address");
            immutableList.add("java.net.Inet6Address");
            immutableList.add("java.net.InetSocketAddress");
            immutableList.add("java.awt.BasicStroke");
            immutableList.add("java.awt.Color");
            immutableList.add("java.awt.GradientPaint");
            immutableList.add("java.awt.LinearGradientPaint");
            immutableList.add("java.awt.RadialGradientPaint");
            immutableList.add("java.awt.Cursor");
            immutableList.add("java.util.regex.Pattern");
        }
    }

    private boolean isImmutable(Field field) {
        boolean isFinal = false;
        if (Modifier.isFinal(field.getModifiers())) {
            isFinal = true;
        }

        if ((field.getType().isPrimitive() || field.getDeclaringClass().isEnum()) && isFinal) {
            return true;
        }

        for (String immutableTypeName : immutableList) {
            if ((field.getType().getName().equals(immutableTypeName)) && isFinal) {
                return true;
            }
        }
        return false;
    }

    private void writeNumOfOrders(List<List<String>> orders, String artifactsDir) {
        String outFilename = Paths.get(artifactsDir, "num-of-orders").toString();
        try (BufferedWriter writer = Writer.getWriter(outFilename)) {
            if (orders != null) {
                int size = orders.size();
                String s = Integer.toString(size);
                writer.write(s);
                writer.write(System.lineSeparator());
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    private static void helper(int[] a, int i) {
        System.arraycopy(a, 0, r[i], 0, a.length);
    }
}
