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
import edu.illinois.starts.helpers.Writer;
import edu.illinois.starts.util.Pair;

import org.apache.commons.codec.binary.Hex;
import org.apache.maven.artifact.DependencyResolutionRequiredException;
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
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;


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

    protected String module;

    protected Map<String, Set<String>> fieldsToTests;

    protected Map<String, Set<String>> testsToFields;

    protected Map<String, List<String>> testClassesToTests;

    protected static String DOT = ".";

    protected static String CLASS_EXTENSION = ".class";

    @Override
    public void execute() {
        superExecute();

        final ErrorLogger logger = new ErrorLogger();
        this.outputPath = PathManager.detectionResults();
        this.coordinates = mavenProject.getGroupId() + ":" + mavenProject.getArtifactId() + ":" + mavenProject.getVersion();

        try {
            defineSettings(logger, mavenProject);
	    String baseDir = mavenProject.getBasedir().toString();
	    if (!module.equals(".") && !baseDir.endsWith(module)) {
                return;
            }
            loadTestRunners(logger, mavenProject);
        } catch (IOException e) {
            e.printStackTrace();
        }
        if (this.runner == null) {
            return;
        }

	long startTime = System.currentTimeMillis();
        try {

            allTestClasses = getTestClasses(mavenProject, this.runner.framework());
            allTestMethods = getTests(mavenProject, this.runner.framework());
	    getPairs();
	    getTestClassesToTests();
            storeOrdersByAsm();
            // storeOrders();
            writeNumOfOrders(orders, artifactsDir);
        } catch (IOException e) {
            e.printStackTrace();
        }
        
	timing(startTime);
        startTime = System.currentTimeMillis();
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
		String baseDir = mavenProject.getBasedir().toString();
		if (!module.equals(".") && !baseDir.endsWith(module)) {
                    return null;
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

    public static String toClassName(String fqn) {
        return fqn.replace(DOT, File.separator) + CLASS_EXTENSION;
    }

    private void getPairs() {
        // System.out.println("PACKAGING: " + mavenProject.getModules());
        // System.exit(0);
        Path path = relativePath(PathManager.modulePath(), Paths.get(pairsFile));
        try {
            Set<String> fieldsList = new HashSet<>();
            Set<String> nonImmutableFields = new HashSet<>();
            BufferedReader in = Files.newBufferedReader(path, StandardCharsets.UTF_8);
            String str;
            while ((str = in.readLine()) != null) {
                // System.out.println(str);
                if (!str.contains(",")) {
		    continue;
		}
		String test = str.substring(0, str.indexOf(','));
                String field = str.substring(str.indexOf(',') + 1);
		if (test.contains("[")) {
		    test = test.substring(0, test.indexOf('['));
		}	
		if (!allTestMethods.contains(test)) {
                    continue;
                }
                Set<String> fieldsSet = testsToFields.getOrDefault(test, new HashSet<>());
                if (fieldsList.contains(field)) {
                    if (nonImmutableFields.contains(field)) {
                        fieldsSet.add(field);
                        testsToFields.put(test, fieldsSet);
                    }
                }
                else {
                    fieldsList.add(field);
                    try {
                        String className = field.substring(0, field.lastIndexOf('.'));
                        String fieldName = field.substring(field.lastIndexOf('.') + 1);
			Class clazz = loader.loadClass(className);
                        URL url = loader.getResource(toClassName(className));
                        if (url == null) {
                            continue;
                        }
                        String extForm = url.toExternalForm();
                        // System.out.println("extForm: " + extForm);
                        if (extForm.startsWith("jar:")) {
                            // System.out.println("extForm");
                            continue;
                        }
                        Field field1 = clazz.getDeclaredField(fieldName);
                        isInside(field1);
                        if (!isImmutable(field1)) {
                            // System.out.println("TEST: " + test + "; " + field);
                            fieldsSet.add(field);
                            nonImmutableFields.add(field);
                            testsToFields.put(test, fieldsSet);
                        }
                    } catch (ClassNotFoundException e) {
                        // e.printStackTrace();
                    } catch (NoSuchFieldException e) {
                        // e.printStackTrace();
                    }
                }
            }
            fieldsToTests = getReverseClosure(testsToFields);
        } catch (IOException e) {
            e.printStackTrace();
        }
        List<String> testsInTestsToFields = new LinkedList<>();
        for (String key : testsToFields.keySet()) {
            testsInTestsToFields.add(key);
        }
        for (int i = 0; i < testsInTestsToFields.size() - 1; i++) {
            for (int j = i + 1; j < testsInTestsToFields.size(); j++) {
                String firstTest = testsInTestsToFields.get(i);
                String secondTest = testsInTestsToFields.get(j);
		Set<String> firstSet = new HashSet<>(testsToFields.get(firstTest));
		Set<String> secondSet = new HashSet<>(testsToFields.get(secondTest));
                firstSet.retainAll(secondSet);
		if (firstSet.size() == 0) {
                    continue;
                }
                String clzName0 = firstTest.substring(0, firstTest.lastIndexOf('.'));
                String clzName1 = secondTest.substring(0, secondTest.lastIndexOf('.'));
                if (!clzName0.equals(clzName1)) {
                    crossClassPairSet.add(new Pair<>(firstTest, secondTest));
                    crossClassPairSet.add(new Pair<>(secondTest, firstTest));
                } else {
                    pairSet.add(new Pair<>(firstTest, secondTest));
                    pairSet.add(new Pair<>(secondTest, firstTest));
                }
            }
        }
        /* for (String key: fieldsToTests.keySet()) {
            Set<String> testsSet = fieldsToTests.get(key);
            List<String> testsList = new LinkedList<>();
            for (String testItem : testsSet) {
                testsList.add(testItem);
            }
            for (int i = 0; i < testsSet.size() - 1; i++) {
                for (int j = i + 1; j < testsSet.size(); j++) {
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
        } */
	writeNumOfPairs(artifactsDir, crossClassPairSet, "num-of-cross-class-pairs");
	writePairs(artifactsDir, crossClassPairSet, "cross-class-pairs");
	writeNumOfPairs(artifactsDir, pairSet, "num-of-intra-class-pairs");
	writePairs(artifactsDir, pairSet, "intra-class-pairs");
    	Set<Pair> allPairs = new HashSet<Pair>();
	allPairs.addAll(crossClassPairSet);
	allPairs.addAll(pairSet);
	writeNumOfPairs(artifactsDir, allPairs, "num-of-all-pairs");
	writePairs(artifactsDir, allPairs, "all-pairs");
    }

    protected void getTestClassesToTests() {
        testClassesToTests = new HashMap<>();
        // System.out.println("ALLTESTSMETHODS: " + allTestMethods.size());
        for (String testItem : allTestMethods) {
            String testItemClass = testItem.substring(0, testItem.lastIndexOf("."));
            List<String> testItemValue = new LinkedList<>();
            if (testClassesToTests.containsKey(testItemClass)) {
                testItemValue = testClassesToTests.get(testItemClass);
            }
            testItemValue.add(testItem);
            testClassesToTests.put(testItemClass, testItemValue);
        }
    }

    private class TestClassEndPoints {
        String testClass;
        String firstTestMethod;
        String lastTestMethod;

        TestClassEndPoints(String testClass, String firstTestMethod, String lastTestMethod) {
            this.testClass = testClass;
            this.firstTestMethod = firstTestMethod;
            this.lastTestMethod = lastTestMethod;
        }

        public void setFirstTestMethod(String firstTestMethod) {
            this.firstTestMethod = firstTestMethod;
        }

        public void setLastTestMethod(String lastTestMethod) {
            this.lastTestMethod = lastTestMethod;
        }
    }

    private List<String> getBestTestMethodOrder(List<String> tests, Set<Pair<String, String>> pairs, TestClassEndPoints endpoints) {
        // the whole intra class order for this test class
        List<String> testMethodOrder = new ArrayList<>();

        // the first part intra class order (from left to right)
        List<String> firstTestMethodOrder = new ArrayList<>();

        // the second part intra class order (from right to left)
        List<String> secondTestMethodOrder = new ArrayList<>();

        // obtain the info from endpoints for this test class
        String testClass = endpoints.testClass;
        String firstTestMethod = endpoints.firstTestMethod;
        String lastTestMethod = endpoints.lastTestMethod;

        // obtain the test size
        int testsSize = tests.size();

        // store the already selected tests when constructing the next longest sequence
        Set<String> alreadySelectedTests = new HashSet<>();

        // store the remaining pairs for this test class
        Set<Pair<String, String>> newPairs = new HashSet<>(pairs);

        List<String> bestTestSequence = new LinkedList<>();

        // System.out.println(endpoints.firstTestMethod + ", " + endpoints.lastTestMethod);
        // System.out.println("TESTS SIZE: " + testsSize);
        // System.out.println("REMAINING PAIRS: " + pairs.size());

        while (alreadySelectedTests.size() < testsSize) {
            // System.out.println("START: " + firstTestMethod + ", " + lastTestMethod);
            if (!firstTestMethod.equals("")) {
                // Trying to link from first method as long as possible
                alreadySelectedTests.add(firstTestMethod);
                bestTestSequence = findBestNextTestSequence(firstTestMethod, newPairs, endpoints.lastTestMethod, alreadySelectedTests, false);

                // get the best sequence from the left, put this partial order at the stored order (from left to right)
                firstTestMethodOrder.addAll(bestTestSequence);

                // need to find the next left sequence from scratch, will random select one
                firstTestMethod = "";
            } else if (!lastTestMethod.equals("")) {
                // Trying to link from last method as long as possible
                alreadySelectedTests.add(lastTestMethod);
                bestTestSequence = findBestNextTestSequence(lastTestMethod, newPairs, endpoints.firstTestMethod, alreadySelectedTests, true);

                // get the best sequence from the left, put this partial order at the stored order (from left to right)
                secondTestMethodOrder.addAll(0, bestTestSequence);

                // need to find the next right sequence from scratch, will random select one
                lastTestMethod = "";
            } else {
                // need to find the next left sequence from scratch, will random select one
                // However, the problem is that the sequence constructed from left may only contain one test
                // the same as the sequence constructed from right
                for (String test : tests) {
                    if (!alreadySelectedTests.contains(test) && !test.equals(firstTestMethod) && !test.equals(lastTestMethod)) {
                        Set<String> newAlreadySelectedTests = new HashSet<>(alreadySelectedTests);
                        newAlreadySelectedTests.add(test);
                        bestTestSequence = findBestNextTestSequence(test, newPairs, endpoints.lastTestMethod, newAlreadySelectedTests, false);
                        break;
                    }
                }
                // If the sequence constructed from left is longer than one, just maintain it.
                if (bestTestSequence.size() > 1) {
                    firstTestMethodOrder.addAll(bestTestSequence);
                    firstTestMethod = "";
                } else if (bestTestSequence.size() == 1) {
                    for (String test : tests) {
                        if (!alreadySelectedTests.contains(test) && !test.equals(firstTestMethod) && !test.equals(lastTestMethod)) {
                            Set<String> newAlreadySelectedTests = new HashSet<>(alreadySelectedTests);
                            newAlreadySelectedTests.add(test);
                            List<String> tmpBestTestSequence = findBestNextTestSequence(test, newPairs, endpoints.firstTestMethod, alreadySelectedTests, true);
                            if (tmpBestTestSequence.size() >= 1) {
                                bestTestSequence = tmpBestTestSequence;
                                secondTestMethodOrder.addAll(0, bestTestSequence);
                                lastTestMethod = "";
                                break;
                            }
                        }
                    }
                }
            }
            // System.out.println(testClass + ": " + bestTestSequence);
            // Filter out the pairs that have already been covered now
            if (bestTestSequence.size() > 0) {
                String firstTest = bestTestSequence.get(0);
                for (int i = 1; i < bestTestSequence.size(); i++) {
                    Pair<String, String> p = new Pair<>(firstTest, bestTestSequence.get(i));
                    newPairs.remove(p);
                    firstTest = bestTestSequence.get(i);
                }
            }
            alreadySelectedTests.addAll(bestTestSequence);
        }
        testMethodOrder.addAll(firstTestMethodOrder);
        testMethodOrder.addAll(secondTestMethodOrder);
        // System.out.println("EQUAL: " + (testMethodOrder.size() == testsSize));
        // System.out.println("METHOD SIZE: " + testMethodOrder.size() + "," + testsSize);
        return testMethodOrder;
    }

    private List<String> findBestNextTestSequence(String test, Set<Pair<String, String>> pairs, String lastTest, Set<String> alreadySelectedTests, boolean reverse) {
        List<String> bestSequence = new LinkedList<>();
        Set<Pair> newPairs = new HashSet<>(pairs);
        if (reverse) {
            bestSequence.add(0, test);
        } else {
            bestSequence.add(test);
        }
        String linkingTest = test;
        while(true) {
            String candidateTest = null;
            for (Pair<String, String> pair : newPairs) {
                // Consider next link based on what pairs need to be covered
                // Next link depends on which direction we are going, forward or backward (reverse)
                if (reverse) {
                    // from right to left
                    if (pair.getValue().equals(linkingTest)) {
                        candidateTest = pair.getKey();
                    }
                } else {
                    // from left to right
                    if (pair.getKey().equals(linkingTest)) {
                        candidateTest = pair.getValue();
                    }
                }
                // Do not link further if already seen this test before or it is the last test based on the endpoint
                if (candidateTest == null) {
                    continue;
                }

                if (alreadySelectedTests.contains(candidateTest) || candidateTest.equals(lastTest)) {
                    candidateTest = null;
                    continue;
                }

                if (candidateTest != null) {
                    break;
                }
            }
            if (candidateTest == null) {
                break;
            } else {
                if (reverse) {
                    bestSequence.add(0, candidateTest);
                    newPairs.remove(new Pair(candidateTest, linkingTest));
                } else {
                    bestSequence.add(candidateTest);
                    newPairs.remove(new Pair(linkingTest, candidateTest));
                }
                linkingTest = candidateTest;
                alreadySelectedTests.add(candidateTest);
            }
        }

        return bestSequence;
    }

    /* private List<String> findBestNextTestSequence(String test, Set<Pair<String, String>> pairs, String lastTest, Set<String> alreadySelectedTests, boolean reverse) {
        List<String> bestSequence = new LinkedList<>();
        // bestSequence.add(test)
        for (Pair<String, String> pair : pairs) {
            // Consider next link based on what pairs need to be covered
            // Next link depends on which direction we are going, forward or backward (reverse)
            String candidateTest = null;
            if (reverse) {
                // from right to left
                if (pair.getValue().equals(test)) {
                    candidateTest = pair.getKey();
                }
            } else {
                // from left to right
                if (pair.getKey().equals(test)) {
                    candidateTest = pair.getValue();
                }
            }
            if (candidateTest == null) {
                continue;
            }
            // Do not link further if already seen this test before or it is the last test based on the endpoint
            if (alreadySelectedTests.contains(candidateTest) || candidateTest.equals(lastTest)) {
                continue;
            }
            Set<Pair<String, String>> newPairs = new HashSet<>(pairs);
            newPairs.remove(pair);
            Set<String> newAlreadySelectedTests = new HashSet<>(alreadySelectedTests);
            newAlreadySelectedTests.add(candidateTest);
            // Try one step further to search for the best sequence assuming linking forward with this candidate test
            List<String> potentialNextBestSequence = findBestNextTestSequence(candidateTest, newPairs, lastTest, newAlreadySelectedTests, reverse);
            if (potentialNextBestSequence.size() > bestSequence.size()) {
                bestSequence = potentialNextBestSequence;
                System.out.println("TMP: " + test + ":" + bestSequence);
            }
        }
        // Return the best sequence that involves the longest sequence going further, but now including the test at the beginning (or end for reverse)
        if (reverse) {
            bestSequence.add(test);
        } else {
            bestSequence.add(0, test);
        }
        return bestSequence;
    } */

    private void storeOrdersByAsm() {
        orders = new LinkedList<>();

        int clazzSize = allTestClasses.size();
        Set<Pair> remainingPairs = new HashSet<>(pairSet);

        Map<String, Set<String>> occurrenceMap = new HashMap<>();
        for (Pair pairItem : remainingPairs) {
            Set<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new HashSet<>());
            valueList.add((String) pairItem.getValue());
            Set<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new HashSet<>());
            keyList.add((String) pairItem.getKey());
        }
        List<Map.Entry<String, Set<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
        // descending order
        Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

        Set<Pair> remainingCrossClassPairs = new HashSet<>(crossClassPairSet);
        // System.out.println("CLAZZSIZE: " + clazzSize);
        while (!remainingCrossClassPairs.isEmpty() || !remainingPairs.isEmpty()) {
            List<String> tmpClassOrder = new LinkedList<>();
            Map<String, TestClassEndPoints> testClassEndPointsMap = new HashMap<>();
            List<String> sequence = new LinkedList<>();
            String lastLeftAddedTest = "";
            String lastRightAddedTest = "";
            Set<String> processedClasses = new HashSet<>();
            int leftIndex = 0;
            int rightIndex = 0;
            boolean leftEnd = false;
            boolean rightEnd = false;
            System.out.println("CrossPairsSize: " + remainingCrossClassPairs.size());
            System.out.println("IntraPairsSize: " + remainingPairs.size());
            /* if (remainingPairs.size() == 2) {
	    	System.out.println(remainingPairs);
	    } */
	    while (processedClasses.size() < clazzSize) {
                Pair pair1 = new Pair("", "");
                if (!leftEnd) {
                    pair1 = getPairs(sequence, tmpClassOrder, lastLeftAddedTest, remainingCrossClassPairs, processedClasses, true);
                }
                if (!pair1.toString().equals("=")) {
                    // System.out.println("lastLeftAddedTest: " + lastLeftAddedTest);
                    // System.out.println("PAIR1: " + pair1.toString());
                    remainingCrossClassPairs.remove(pair1);
                    if (sequence.contains(lastLeftAddedTest)) {
                        leftIndex = sequence.indexOf(lastLeftAddedTest);
                    }
                    if (sequence.contains(lastRightAddedTest)) {
                        rightIndex = sequence.indexOf(lastRightAddedTest);
                    }
                    lastLeftAddedTest = pair1.getKey().toString();
                    String test2 = pair1.getValue().toString();;
                    // System.out.println("LEFT INDEX: " + leftIndex);
                    String c1 = lastLeftAddedTest.substring(0, lastLeftAddedTest.lastIndexOf('.'));
                    if (!test2.equals("LAST")) {
                        String c2 = test2.substring(0, test2.lastIndexOf('.'));
                        sequence.add(leftIndex, test2);
                        processedClasses.add(c2);
                        if (testClassEndPointsMap.containsKey(c2)) {
                            TestClassEndPoints testClassEndPoints = testClassEndPointsMap.get(c2);
                            testClassEndPoints.setFirstTestMethod(test2);
                        } else {
                            testClassEndPointsMap.put(c2, new TestClassEndPoints(c2, test2, ""));
                        }
                    }
                    sequence.add(leftIndex, lastLeftAddedTest);
                    processedClasses.add(c1);
                    if (testClassEndPointsMap.containsKey(c1)) {
                        TestClassEndPoints testClassEndPoints = testClassEndPointsMap.get(c1);
                        testClassEndPoints.setLastTestMethod(lastLeftAddedTest);
                    } else {
                        testClassEndPointsMap.put(c1, new TestClassEndPoints(c1, "", lastLeftAddedTest));
                    }
                    if (!test2.equals("LAST")) {
                        if (rightIndex < sequence.indexOf(test2)) {
                            lastRightAddedTest = test2;
                            rightIndex = sequence.indexOf(test2);
                        }
                    }

                    // System.out.println("PAIR1: " + pair1.toString());
                    // System.out.println("PROCLAZZSIZE: " + processedClasses.size());
                } else {
                    leftEnd = true;
                }
                Pair pair2 = new Pair("", "");
                if (!rightEnd) {
                    pair2 = getPairs(sequence, tmpClassOrder, lastRightAddedTest, remainingCrossClassPairs, processedClasses, false);
                }
                if (!pair2.toString().equals("=")) {
                    // System.out.println("lastRightAddedTest: " + lastRightAddedTest);
                    // System.out.println("PAIR2: " + pair2.toString());
                    remainingCrossClassPairs.remove(pair2);
                    if (sequence.contains(lastRightAddedTest)) {
                        rightIndex = sequence.indexOf(lastRightAddedTest);
                    }
                    String test1 = pair2.getKey().toString();
                    lastRightAddedTest = pair2.getValue().toString();
                    // System.out.println("RIGHT INDEX: " + rightIndex);
                    String c2 = lastRightAddedTest.substring(0, lastRightAddedTest.lastIndexOf('.'));
                    if (!test1.equals("LAST")) {
                        String c1 = test1.substring(0, test1.lastIndexOf('.'));
                        sequence.add(rightIndex + 1, test1);
                        sequence.add(rightIndex + 2, lastRightAddedTest);
                        processedClasses.add(c1);
                        if (testClassEndPointsMap.containsKey(c1)) {
                            TestClassEndPoints testClassEndPoints = testClassEndPointsMap.get(c1);
                            testClassEndPoints.setLastTestMethod(test1);
                        } else {
                            testClassEndPointsMap.put(c1, new TestClassEndPoints(c1, "", test1));
                        }
                    } else {
                        sequence.add(rightIndex + 1, lastRightAddedTest);
                    }
                    processedClasses.add(c2);
                    if (testClassEndPointsMap.containsKey(c2)) {
                        TestClassEndPoints testClassEndPoints = testClassEndPointsMap.get(c2);
                        testClassEndPoints.setFirstTestMethod(lastRightAddedTest);
                    } else {
                        testClassEndPointsMap.put(c2, new TestClassEndPoints(c2, lastRightAddedTest, ""));
                    }
                    if (!test1.equals("LAST")) {
                        if (leftIndex > sequence.indexOf(test1)) {
                            lastLeftAddedTest = test1;
                            leftIndex = sequence.indexOf(test1);
                        }
                    }
                    // System.out.println("PAIR2: " + pair2.toString());
                    // System.out.println("PROCLAZZSIZE: " + processedClasses.size());
                } else {
                    rightEnd = true;
                }
		// System.out.println(leftEnd + "," + rightEnd);
                // .println(clazzSize + ", " + processedClasses.size());
                if (leftEnd && rightEnd || (processedClasses.size() == clazzSize)) {
                    // System.out.println("SEQUENCE SIZE: " + sequence.size());
                    if (processedClasses.size() != clazzSize) {
                        if (sequence.size() == 0) {
                            for (String testClass : testClassesToTests.keySet()) {
                                if (!processedClasses.contains(testClass)) {
                                    List<String> tests = testClassesToTests.get(testClass);
                                    for (String test : tests) {
                                        if (!tmpClassOrder.contains(test)) {
                                            // System.out.println("HAHAHA");
                                            sequence.add("class:" + testClass);
                                            processedClasses.add(testClass);
                                            if (!testClassEndPointsMap.containsKey(testClass)) {
                                                testClassEndPointsMap.put(testClass, new TestClassEndPoints(testClass, "", ""));
                                            }
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    tmpClassOrder.addAll(sequence);
                    sequence = new LinkedList<>();
                    lastLeftAddedTest = "";
                    lastRightAddedTest = "";
                    leftIndex = 0;
                    rightIndex = 0;
                    leftEnd = false;
                    rightEnd = false;
                }
            }
            // System.out.println("ORDER: " + tmpClassOrder);
            // System.out.println("REMAINING PAIRS: " + remainingCrossClassPairs);
            List<String> classSequence = new LinkedList<>();
            for (String testInOrder : tmpClassOrder) {
                String testClassInOrder = testInOrder.substring(0, testInOrder.lastIndexOf("."));
                if (testInOrder.startsWith("class:")) {
                    testClassInOrder = testInOrder.substring(6);
                }
                if (!classSequence.contains(testClassInOrder)) {
                    classSequence.add(testClassInOrder);
                }
            }
            /* for (String cl : allTestClasses) {
                if (!classSequence.contains(cl)) {
                    System.out.println("NOT CAP: " + cl);
                }
            } */
            // System.out.println("classSequence: " + classSequence);
            // System.out.println("testClassEndPointsMap size: " + testClassEndPointsMap.size());
            List<String> order = new LinkedList<>();
            for (String clazz : classSequence) {
                if (testClassEndPointsMap.containsKey(clazz)) {
                    TestClassEndPoints testClassEndPoints = testClassEndPointsMap.get(clazz);
                    // System.out.println("clazz: " + testClassEndPoints.firstTestMethod + ", " + testClassEndPoints.lastTestMethod);
                    List<String> testsInThisClass = testClassesToTests.get(clazz);
                    Set<Pair<String, String>> filteredPairs = new HashSet<>();
                    // System.out.println("tests size: " + testsInThisClass.size());
                    // System.out.println("pairs size: " + remainingPairs.size());
                    for (Pair pair : remainingPairs) {
                        String test1 = pair.getKey().toString();
                        String testClass = test1.substring(0, test1.lastIndexOf("."));
                        if (testClass.equals(clazz)) {
                            filteredPairs.add(pair);
                        }
                    }
                    // System.out.println("filtered pairs size: " + filteredPairs.size());
		    List<String> bestSequence = getBestTestMethodOrder(testsInThisClass, filteredPairs, testClassEndPoints);
                    /* if (clazz.equals("org.springframework.boot.actuate.autoconfigure.metrics.test.MetricsIntegrationTests")) {
                    	System.out.println(bestSequence);
			System.out.println(testClassEndPoints.firstTestMethod + ", " +  testClassEndPoints.lastTestMethod);
		    } */
		    order.addAll(bestSequence);
                    // System.out.println("tmp: " + order.size());
                }
            }
            // List<String> reverseOrder = new LinkedList<>(order);
            // Collections.reverse(reverseOrder);
            if (order.size() == 0) {
                System.exit(0);
            }
            String firstTest = order.get(0);
            for (int i = 1; i < order.size(); i++) {
                Pair<String, String> p = new Pair<>(firstTest, order.get(i));
                remainingCrossClassPairs.remove(p);
                remainingPairs.remove(p);
                firstTest = order.get(i);
            }
            /* String firstTestInReverse = reverseOrder.get(0);
            for (int i = 1; i < reverseOrder.size(); i++) {
                Pair<String, String> p = new Pair<>(firstTestInReverse, reverseOrder.get(i));
                remainingCrossClassPairs.remove(p);
                remainingPairs.remove(p);
                firstTestInReverse = reverseOrder.get(i);
            } */
            // System.out.println("ORDER SIZE: " + order.size());
            orders.add(order);
            // System.out.println("ORDERSSIZE: " + orders.size());
            // System.out.println("SIZE: " + order.size());
            // orders.add(reverseOrder);
            // System.exit(0);
            // order.addAll(sequence);
        }
        System.out.println("ORDERSSIZE: " + orders.size());
        int index = 0;
        for(List<String> orderItem : orders) {
            writeOrder(orderItem, artifactsDir, index);
            index ++;
        }
    }

    private void storeOrders() {
        // put both the intra class pairs and cross class pairs here
        Set<Pair> remainingPairs = new HashSet<>(pairSet);
        remainingPairs.addAll(crossClassPairSet);
        // System.out.println("INITIAL REMAINING PAIRS: " + remainingPairs.size());

        // transfer the TuscanSquare to be actual orders
        List<List<String>> transformedOrders = new LinkedList<>(orders);

        // get new orders based on the pairs that are covered
        orders = new LinkedList<>();

        // store the order to pair map to speed up
        Map<Integer, Set<Pair>> orderToPairs = new HashMap<>();
        for (int i = 0 ; i < transformedOrders.size() ; i++) {
            List<String> orderItem = transformedOrders.get(i);
            Set<Pair> pairsList = new HashSet<>();
            for (int j = 0 ; j < orderItem.size() - 1 ; j++) {
                Pair toBeRemoved = new Pair<>(orderItem.get(j), orderItem.get(j + 1));
                if (remainingPairs.contains(toBeRemoved)) {
                    pairsList.add(toBeRemoved);
                }
            }
            orderToPairs.put(i, pairsList);
        }

        // record if this order is used to speed up
        Set<Integer> used = new HashSet<>();

        // deal with the other orders
        while (!remainingPairs.isEmpty()) {
            // System.out.println("REMAINING PAIRS SIZE: " + remainingPairs.size());
            int maxAdditionalSize = 0;
            int maxIndex = 0;

            // for each order, check if the union set size with remaining pairs is larger than the current one
            for (int i = 0 ; i < transformedOrders.size() ; i++) {
                // if used, then skip
                if (used.contains(i)) {
                    continue;
                }

                // use set to speed up
                Set<Pair> orderToPair = orderToPairs.get(i);
                Set<Pair> pairsSet = new HashSet<>();
                pairsSet.addAll(orderToPair);
                pairsSet.retainAll(remainingPairs);
                int potentialSize = pairsSet.size();
                if (potentialSize > maxAdditionalSize) {
                    maxAdditionalSize = potentialSize;
                    maxIndex = i;
                }
            }
            if (transformedOrders.size() == used.size()) {
                System.out.println("Exception: There are still some remaining pairs but orders have been created!");
                break;
            }
            if (!used.contains(maxIndex)) {
                used.add(maxIndex);
                List<String> maxOrder = transformedOrders.get(maxIndex);
                orders.add(maxOrder);
                remainingPairs.removeAll(orderToPairs.get(maxIndex));
                // System.out.println("finalMaxAdditionalSize(change to): " + maxAdditionalSize);
            }
        }
        // System.out.println("FINAL NUM OF ORDERS: " + orders.size());
    }

    protected Pair getPairs(List<String> sequence, List<String> order, String lastAddedTest, Set<Pair> remainingPairs, Set<String> processedClasses, boolean left) {
        Map<String, List<String>> occurrenceMap = new HashMap<>();
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

	/* Map<String, Integer> testClassesToTimes = new HashMap<>();
        for (int i = 0; i < occurrenceSortedList.size(); i++) {
            String firstTest = occurrenceSortedList.get(i).getKey();
	    String firstTestClazz = firstTest.substring(0, firstTest.lastIndexOf('.'));
            if (!testClassesToTimes.containsKey(firstTestClazz)) {
	    	testClassesToTimes.put(firstTestClazz, occurrenceSortedList.get(i).getValue().size());
	    } else {
		Integer num = testClassesToTimes.get(firstTestClazz);
		testClassesToTimes.put(firstTestClazz, num + occurrenceSortedList.get(i).getValue().size());
	    }
	    // System.out.println(firstTest + ": " + occurrenceSortedList.get(i).getValue().size());
        }
	List<Map.Entry<String, Integer>> testClassesToTimesList = new ArrayList<>(testClassesToTimes.entrySet());
        // descending sequence
        Collections.sort(testClassesToTimesList, (o1, o2) -> (o2.getValue() - o1.getValue()));
	for (int i = 0; i < testClassesToTimesList.size(); i++) {
	    System.out.println(testClassesToTimesList.get(i).getKey() + ": " + testClassesToTimesList.get(i).getValue());
	}
        System.exit(0); */
        String lastAddedTestClass = "";
        if (!lastAddedTest.equals("")) {
            lastAddedTestClass = lastAddedTest.substring(0, lastAddedTest.lastIndexOf('.'));
        }

        if (left) {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String firstTest = occurrenceSortedList.get(i).getKey();
                /* if (lastAddedTest.equals("") && order.size() == 0) {
                    System.out.println("BEST TEST IS " + firstTest + " WITH SCORE " + occurrenceSortedList.get(i).getValue().size());
                } */
                String firstTestClass = firstTest.substring(0, firstTest.lastIndexOf('.'));
                if (!testClassesToTests.containsKey(firstTestClass)) {
                    continue;
                }
		if (((!sequence.contains(firstTest) && !order.contains(firstTest)) || testClassesToTests.get(firstTestClass).size() == 1) && (firstTestClass.equals(lastAddedTestClass) || (lastAddedTest.equals("") && !processedClasses.contains(firstTestClass)))) {
                    for (String item : occurrenceSortedList.get(i).getValue()) {
                    // for (int j = 0; j < occurrenceSortedList.size(); j++) { // String item : occurrenceSortedList.get(i).getValue()) {
                        // if (occurrenceSortedList.get(i).getValue().contains(occurrenceSortedList.get(j).getKey())) {
                        //     String item = occurrenceSortedList.get(j).getKey();
			    String itemClass = item.substring(0, item.lastIndexOf('.'));
			    Pair pair = new Pair<>(item, firstTest);
			    /* if (order.size() == 0) {
                                System.out.println("???Left: " + item + ", " + firstTest + " " + remainingPairs.contains(new Pair<>(item, firstTest)));
                                System.out.println(processedClasses.contains(itemClass));
                            } */
                            if ((!sequence.contains(firstTest) && !order.contains(firstTest)) && !processedClasses.contains(itemClass)) {
                                if (remainingPairs.contains(pair)) {
                                    return pair;
                                }
                            } 
			    if ((sequence.contains(firstTest) || order.contains(firstTest)) && !processedClasses.contains(itemClass)  && testClassesToTests.get(firstTestClass).size() == 1) {
			        if (remainingPairs.contains(pair)) {
				    return new Pair<>(item, "LAST");
				}
			    } 
                        // }
                    }
                }
            }
            // release restriction
            /* if (lastAddedTest.equals("")) {
                String firstItem = "";
                for (String testClassItem : testClassesToTests.keySet()) {
                    if (!processedClasses.contains(testClassItem)) {
                        for (String testItem : testClassesToTests.get(testClassItem)) {
                            if (!sequence.contains(testItem) && !order.contains(testItem)) {
                                firstItem = testItem;
                                break;
                            }
                        }
                    }
                }
                String firstTestClass = firstItem.substring(0, firstItem.lastIndexOf('.'));
                String secondItem = "";
                for (String testClassItem : testClassesToTests.keySet()) {
                    if (!processedClasses.contains(testClassItem) && !testClassItem.equals(firstTestClass)) {
                        for (String testItem : testClassesToTests.get(testClassItem)) {
                            if (!sequence.contains(testItem) && !order.contains(testItem)) {
                                secondItem = testItem;
                                break;
                            }
                        }
                    }
                }
                if (!firstItem.equals("") && !secondItem.equals("")) {
                    return new Pair<>(secondItem, firstItem);
                }
            } */
        } else {
            for (int i = 0; i < occurrenceSortedList.size(); i++) {
                String firstTest = occurrenceSortedList.get(i).getKey();
                /* if (lastAddedTest.equals("") && order.size() == 0) {
                    System.out.println("BEST TEST IS " + firstTest + " WITH SCORE " + occurrenceSortedList.get(i).getValue().size());
                } */
                String firstTestClass = firstTest.substring(0, firstTest.lastIndexOf('.'));
                // System.out.println("!!!" + firstTestClass);
		if (!testClassesToTests.containsKey(firstTestClass)) {
		    continue;
		}
		// System.out.println("???: " + testClassesToTests.get(firstTestClass));
		if (((!sequence.contains(firstTest) && !order.contains(firstTest)) || testClassesToTests.get(firstTestClass).size() == 1) && (firstTestClass.equals(lastAddedTestClass) || (lastAddedTest.equals("") && !processedClasses.contains(firstTestClass)))) {
                    for (String item : occurrenceSortedList.get(i).getValue()) {
                    // for (int j = 0; j < occurrenceSortedList.size(); j++) { // String item : occurrenceSortedList.get(i).getValue()) {
                    //     if (occurrenceSortedList.get(i).getValue().contains(occurrenceSortedList.get(j).getKey())) {
                    //         String item = occurrenceSortedList.get(j).getKey();
                            String itemClass = item.substring(0, item.lastIndexOf('.'));
			    Pair pair = new Pair<>(firstTest, item);
			    /* if (order.size() == 0) {
                                System.out.println("???Right: " + firstTest + ", " + item + " " + remainingPairs.contains(new Pair<>(firstTest, item)));
                                System.out.println(processedClasses.contains(itemClass));
                            } */
			    if ((!sequence.contains(firstTest) && !order.contains(firstTest)) && !processedClasses.contains(itemClass)) {
                                if (remainingPairs.contains(pair)) {
                                    return pair;
                                }
                            }
                            if ((sequence.contains(firstTest) || order.contains(firstTest)) && !processedClasses.contains(itemClass) && testClassesToTests.get(firstTestClass).size() == 1) {
                                if (remainingPairs.contains(pair)) {
				    return new Pair<>("LAST", item);
				}
                            }
			// }
                    }
                }
            }
            // release restriction
            /* if (lastAddedTest.equals("")) {
                String firstItem = "";
                for (String testClassItem : testClassesToTests.keySet()) {
                    if (!processedClasses.contains(testClassItem)) {
                        for (String testItem : testClassesToTests.get(testClassItem)) {
                            if (!sequence.contains(testItem) && !order.contains(testItem)) {
                                firstItem = testItem;
                                break;
                            }
                        }
                    }
                }
                String firstTestClass = firstItem.substring(0, firstItem.lastIndexOf('.'));
                String secondItem = "";
                for (String testClassItem : testClassesToTests.keySet()) {
                    if (!processedClasses.contains(testClassItem) && !testClassItem.equals(firstTestClass)) {
                        for (String testItem : testClassesToTests.get(testClassItem)) {
                            if (!sequence.contains(testItem) && !order.contains(testItem)) {
                                secondItem = testItem;
                                break;
                            }
                        }
                    }
                }
                if (!firstItem.equals("") && !secondItem.equals("")) {
                    return new Pair<>(firstItem, secondItem);
                }
            } */
        }
        return new Pair<>("", "");
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
 	module = Configuration.config().getProperty("dt.asm.module", "");	

        artifactsDir = getArtifactsDir();
        testsToFields = new HashMap();
        fieldsToTests = new HashMap();

        pairSet = new HashSet<>();
        crossClassPairSet = new HashSet<>();

        getImmutableList();

        getSureFireClassPath(project);
        loader = createClassLoader(sureFireClassPath);
        // getPairs();
        // System.out.println(crossClassPairSet.size());
        // System.out.println(pairSet.size());
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

    private boolean isInside(Field field) {
        boolean isInside = false;

        // if (field.getDeclaringClass())
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


    private void writeOrder(List<String> order, String artifactsDir, int index) {
        String outFilename = Paths.get(artifactsDir + "/orders", "order-" + index).toString();
        try (BufferedWriter writer = Writer.getWriter(outFilename)) {
            for (String test : order) {
                int i = allTestMethods.indexOf(test);
	        String s = Integer.toString(i);	
		writer.write(s);
                writer.write(System.lineSeparator());
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    private void writeNumOfPairs(String artifactsDir, Set<Pair> pairSet, String fileName) {
        String outFilename = Paths.get(artifactsDir, fileName).toString();
        try (BufferedWriter writer = Writer.getWriter(outFilename)) {
            if (pairSet != null) {
                int size = pairSet.size();
                String s = Integer.toString(size);
                writer.write(s);
                writer.write(System.lineSeparator());
            }
	} catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    private void writePairs(String artifactsDir, Set<Pair> pairSet, String fileName) {
        String outFilename = Paths.get(artifactsDir, fileName).toString();
        try (BufferedWriter writer = Writer.getWriter(outFilename)) {
            for (Pair pair : pairSet) {
                writer.write(pair.getKey() + "," + pair.getValue());
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
