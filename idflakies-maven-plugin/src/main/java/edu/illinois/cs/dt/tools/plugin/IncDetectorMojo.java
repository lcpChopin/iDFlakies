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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;

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

    private List<String> allTestMethods;

    private List<String> finalSelectedTests;

    private Set<Pair> pairSet;

    private Set<Pair> classesPairSet;

    private static int[][] r;

    private List<List<String>> orders;

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
        long startTime = System.currentTimeMillis();
        try {
            affectedTestClasses = computeAffectedTests(mavenProject);
            if (!detectOrNot) {
                System.out.println("Not detect flaky tests at the first run");
                return;
            }
        } catch (IOException | MojoExecutionException | ClassNotFoundException e) {
            e.printStackTrace();
        }
        timing(startTime);

        try {
            finalSelectedTests = getTests(mavenProject, this.runner.framework());
            // storeOrders();
            storeOrdersByClasses();
            // storeOrdersBasedOnSymmetric();
            // storeClassesOrdersBasedOnSymmetric();
        } catch (IOException e) {
            e.printStackTrace();
        }

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
                detector = DetectorFactory.makeDetector(this.runner, mavenProject.getBasedir(), tests, rounds, orders);
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

    // TODO: make Starts and Ekstazi's deps similar
    private Set<String> computeAffectedTests(final MavenProject project) throws IOException, MojoExecutionException, ClassNotFoundException {
        Set<String> affectedTests = new HashSet<>();
        Set<String> allTests = new HashSet<>(getTestClasses(project, this.runner.framework()));

        selectedTests = getSelectedTests();
        // check if the classpath or jar checksum are changed; if they are changed, STARTs/ekstazi should select all tests
        checkSelectAll();

        affectedTests.addAll(selectedTests);
        if (!selectMore) {
            return affectedTests;
        }

        if (selectAll) {
            return allTests;
        }

        getTransitiveClosure();

        Set<String> additionalTests = new HashSet<>();

        // iter through the affected tests and find what each one depends on
        Set<String> processedClasses = new HashSet<>();

        allTestMethods = super.getTests(mavenProject, this.runner.framework());
        pairSet = new HashSet<>();
        classesPairSet = new HashSet<>();


        getImmutableList();
        for (String affectedTest : affectedTests) {
            Set<String> dependencies = transitiveClosure.get(affectedTest);
            if (dependencies == null) {
                continue;
            }
            for (String dependency : dependencies) {
                if (processedClasses.contains(dependency)) {
                    continue;
                }
                try {
                    Class clazz = loader.loadClass(dependency);
                    for (Field field : clazz.getDeclaredFields()) {
                        if (isImmutable(field) && Modifier.isFinal(field.getModifiers())) {
                            continue;
                        }
                        if (Modifier.isStatic(field.getModifiers())) {
                            String upperLevelAffectedClass = clazz.getName();
                            Set<String> upperLevelAffectedTestClasses = reverseTransitiveClosure.get(upperLevelAffectedClass);
                            List<String> upperLevelAffectedTestClassesList = new LinkedList<>();
                            if (upperLevelAffectedTestClasses != null) {
                                List<String> upperLevelAffectedTestsList = new ArrayList<>();
                                for (String upperLevelAffectedTestClass : upperLevelAffectedTestClasses) {
                                    additionalTests.add(upperLevelAffectedTestClass);
                                    upperLevelAffectedTestClassesList.add(upperLevelAffectedTestClass);
                                    for (String test : allTestMethods) {
                                        if (test.startsWith(upperLevelAffectedTestClass) & !upperLevelAffectedTestsList.contains(test)) {
                                            upperLevelAffectedTestsList.add(test);
                                        }
                                    }
                                }
                                for (int i = 0; i < upperLevelAffectedTestClassesList.size() - 1; i++) {
                                    for (int j = i + 1; j < upperLevelAffectedTestClassesList.size(); j++) {
                                        Pair<String, String> pair1 = new Pair<>(upperLevelAffectedTestClassesList.get(i), upperLevelAffectedTestClassesList.get(j));
                                        Pair<String, String> pair2 = new Pair<>(upperLevelAffectedTestClassesList.get(j), upperLevelAffectedTestClassesList.get(i));
                                        if (!classesPairSet.contains(pair1)) {
                                            classesPairSet.add(pair1);
                                        }
                                        if (!classesPairSet.contains(pair2)) {
                                            classesPairSet.add(pair2);
                                        }
                                    }
                                }
                                System.out.println("NUM of Tests for class " + clazz + ": " + upperLevelAffectedTestsList.size());
                                for (int i = 0; i < upperLevelAffectedTestsList.size() - 1; i++) {
                                    for (int j = i + 1; j < upperLevelAffectedTestsList.size(); j++) {
                                        Pair<String, String> pair1 = new Pair<>(upperLevelAffectedTestsList.get(i), upperLevelAffectedTestsList.get(j));
                                        Pair<String, String> pair2 = new Pair<>(upperLevelAffectedTestsList.get(j), upperLevelAffectedTestsList.get(i));
                                        if (!pairSet.contains(pair1)) {
                                            pairSet.add(pair1);
                                        }
                                        if (!pairSet.contains(pair2)) {
                                            pairSet.add(pair2);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                    processedClasses.add(dependency);
                } catch (ClassNotFoundException | NoClassDefFoundError e)  {
                    e.printStackTrace();
                }
            }
        }

        affectedTests.addAll(additionalTests);
        System.out.println("WHOLE NUMBER OF PAIRS: " + allTestMethods.size() * (allTestMethods.size() - 1));
        System.out.println("SELECTED NUMBER OF PAIRS: " + pairSet.size());
        return affectedTests;
    }

    private void storeOrders() {
        // obtain the TuscanSquare for the size of tests
        int n = finalSelectedTests.size();
        generateTuscanSquare(n);
        Set<Pair> remainingPairs = new HashSet<>(pairSet);
        System.out.println("INITIAL REMAINING PAIRS: " + remainingPairs.size());

        // transfer the TuscanSquare to be actual orders
        List<List<String>> transformedOrders = new LinkedList<>();
        for (int[] ri : r) {
            List<String> oneOrder = new LinkedList<>();
            for (int index = 0; index < ri.length - 1; index ++) {
                oneOrder.add(finalSelectedTests.get(ri[index]));
            }
            transformedOrders.add(oneOrder);
        }

        // deal with the first order
        orders = new LinkedList<>();
        /* List<String> firstOrder = transformedOrders.get(0);
        orders.add(firstOrder);
        for (int i = 0 ; i < firstOrder.size() - 1 ; i++) {
            Pair toBeRemoved = new Pair<>(firstOrder.get(i), firstOrder.get(i + 1));
            remainingPairs.remove(toBeRemoved);
        }
        transformedOrders.remove(0); */

        // deal with the other orders
        while (!remainingPairs.isEmpty()) {
            int maxAdditionalSize = 0;
            int initialSize = remainingPairs.size();
            System.out.println("INITIAL SIZE: " + initialSize);
            int maxIndex = 0;
            for (int i = 0 ; i < transformedOrders.size() ; i++) {
                List<String> orderItem = transformedOrders.get(i);
                Set<Pair> finalRemainingPairs = new HashSet<>(remainingPairs);
                for (int j = 0 ; j < orderItem.size() - 1 ; j++) {
                    Pair toBeRemoved = new Pair<>(orderItem.get(j), orderItem.get(j + 1));
                    finalRemainingPairs.remove(toBeRemoved);
                }
                int finalSize = finalRemainingPairs.size();
                if (initialSize - finalSize > maxAdditionalSize) {
                    maxAdditionalSize = initialSize - finalSize;
                    maxIndex = i;
                    // System.out.println("maxAdditionalSize(change to): " + maxAdditionalSize);
                }
            }
            List<String> maxOrder = transformedOrders.get(maxIndex);
            orders.add(maxOrder);
            for (int k = 0 ; k < maxOrder.size() - 1 ; k++) {
                Pair toBeRemoved = new Pair<>(maxOrder.get(k), maxOrder.get(k + 1));
                remainingPairs.remove(toBeRemoved);
            }
            System.out.println("finalMaxAdditionalSize(change to): " + maxAdditionalSize);
            // System.out.println("finalOrder: " + maxOrder.toString());
            transformedOrders.remove(maxIndex);
        }

        System.out.println("FINAL NUM OF ORDERS: " + orders.size());
    }

    private void storeOrdersBasedOnSymmetric() {
        orders = new LinkedList<>();

        int n = finalSelectedTests.size();
        /* int middle = 0;
        if (n % 2 == 1) {
            middle = (n - 1) / 2;
        } else {
            middle = n / 2;
        } */
        Set<Pair> remainingPairs = new HashSet<>(pairSet);
        Set<Pair> symmetricRemainingPairs = new HashSet<>(pairSet);

        Map<String, List<String>> occurrenceMap = new HashedMap();
        for (Pair pairItem : remainingPairs) {
            List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
            valueList.add((String) pairItem.getValue());
            occurrenceMap.put((String) pairItem.getKey(), valueList);
            List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
            keyList.add((String) pairItem.getKey());
            occurrenceMap.put((String) pairItem.getValue(), keyList);
        }
        Map<String, List<String>> occurrenceMapDefault = new HashedMap(occurrenceMap);
        List<Map.Entry<String, List<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
        // descending order
        Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

        // deal with the other orders
        while (!remainingPairs.isEmpty()) {
            System.out.println("REMAINING PAIRS SIZE: " + remainingPairs.size());
            System.out.println("SEMMETRIC REMAINING PAIRS SIZE: " + symmetricRemainingPairs.size());
            System.out.println("CURRENT ORDER SIZE: " + orders.size());
            occurrenceMap = new HashedMap();
            // Set<Pair> tmpPairs = new HashSet<>(remainingPairs);
            for (Pair pairItem : remainingPairs) {
                List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
                valueList.add((String) pairItem.getValue());
                occurrenceMap.put((String) pairItem.getKey(), valueList);
                List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
                keyList.add((String) pairItem.getKey());
                occurrenceMap.put((String) pairItem.getValue(), keyList);
            }
            occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
            // descending order
            Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

            // System.out.println("PRINT:" + occurrenceSortedList.toString());
            // List<Map.Entry<String, List<String>>> occurrenceSymmetricSortedList = new ArrayList<>(occurrenceSortedList);

            List<String> order = new LinkedList<>();
            order.add(0, occurrenceSortedList.get(0).getKey());
            int leftBorder = 0;
            int rightBorder = 1;
            String leftItem = occurrenceSortedList.get(0).getKey();
            String rightItem = occurrenceSortedList.get(0).getKey();
            // occurrenceSortedList.remove(0);

            // int filled = 1;
            int s = 0;
            boolean leftEnd = false;
            boolean rightEnd = false;
            while (order.size() < n) {
                // System.out.println(remainingPairs.toString());
                if (!leftEnd) {
                    int i = 0;
                    boolean found = false;
                    if (!symmetricRemainingPairs.isEmpty() && !found) {
                        for (i = 0; i < occurrenceSortedList.size(); i++) {
                            if (occurrenceSortedList.get(i).getKey().equals(leftItem)) {
                                continue;
                            }
                            List<String> leftValue = occurrenceMapDefault.getOrDefault(leftItem, new LinkedList<>());
                            // current test that has most pairs with other tests
                            String tmp = occurrenceSortedList.get(i).getKey();
                            Pair toBeRemoved = new Pair<>(tmp, leftItem);
                            if (leftValue.contains(tmp) && symmetricRemainingPairs.contains(toBeRemoved) && remainingPairs.contains(toBeRemoved) && !order.contains(tmp)) {
                                order.add(leftBorder, tmp);
                                remainingPairs.remove(toBeRemoved);
                                symmetricRemainingPairs.remove(toBeRemoved);
                                Pair reverseToBeRemoved = new Pair<>(leftItem, tmp);
                                symmetricRemainingPairs.remove(reverseToBeRemoved);
                                leftItem = tmp;
                                System.out.println("LEFTINDEX?: " + tmp);
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!remainingPairs.isEmpty() && !found) {
                        for (i = 0; i < occurrenceSortedList.size(); i++) {
                            if (occurrenceSortedList.get(i).getKey().equals(leftItem)) {
                                continue;
                            }
                            List<String> leftValue = occurrenceMapDefault.getOrDefault(leftItem, new LinkedList<>());
                            // current test that has most pairs with other tests
                            String tmp = occurrenceSortedList.get(i).getKey();
                            Pair toBeRemoved = new Pair<>(tmp, leftItem);
                            if (leftValue.contains(tmp) && remainingPairs.contains(toBeRemoved) && !order.contains(tmp)) {
                                order.add(leftBorder, tmp);
                                remainingPairs.remove(toBeRemoved);
                                leftItem = tmp;
                                System.out.println("LEFTINDEX??: " + tmp);
                                found = true;
                                break;
                            }
                        }
                        System.out.println("REACH remainingPairs");
                    }
                    if (found) {
                        // filled ++;
                        rightBorder ++;
                        System.out.println("new left item: " + leftItem + "; " + (s++));
                    } else {
                        leftEnd = true;
                        if (rightEnd) {
                            int j = 0;
                            if (occurrenceSortedList.size() > 0) {
                                while (order.contains(occurrenceSortedList.get(j).getKey())) {
                                    j++;
                                    if (j == occurrenceSortedList.size()) {
                                        break;
                                    }
                                }
                                if (j != occurrenceSortedList.size()) {
                                    leftEnd = false;
                                    rightEnd = false;
                                    leftItem = occurrenceSortedList.get(j).getKey();
                                    rightItem = occurrenceSortedList.get(j).getKey();
                                    order.add(leftBorder, leftItem);
                                    System.out.println("NEWLEFTINDEX???: " + leftItem);
                                    System.out.println("BORDER???: " + leftBorder + " " + rightBorder);
                                    leftBorder = rightBorder;
                                    rightBorder = rightBorder + 1;
                                    // filled++;
                                }
                            }
                            if (j == occurrenceSortedList.size() || occurrenceSortedList.size() == 0) {
                                for (String finalSelectedTest : finalSelectedTests) {
                                    if (!order.contains(finalSelectedTest)) {
                                        order.add(leftBorder, finalSelectedTest);
                                        System.out.println("LEFTINDEX???: " + finalSelectedTest);
                                        leftItem = finalSelectedTest;
                                        rightItem = finalSelectedTest;
                                        leftBorder = rightBorder;
                                        rightBorder = rightBorder + 1;
                                        // filled ++;
                                        leftEnd = false;
                                        rightEnd = false;
                                        break;
                                    }
                                }
                            }
                            // continue;
                        }
                        System.out.println("REACH NOT FOUND");
                    }
                    occurrenceMap = new HashedMap();
                    // Set<Pair> tmpPairs = new HashSet<>(remainingPairs);
                    for (Pair pairItem : remainingPairs) {
                        List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
                        valueList.add((String) pairItem.getValue());
                        occurrenceMap.put((String) pairItem.getKey(), valueList);
                        List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
                        keyList.add((String) pairItem.getKey());
                        occurrenceMap.put((String) pairItem.getValue(), keyList);
                    }
                    occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                }
                if (!rightEnd) {
                    int i = 0;
                    boolean found = false;
                    if (!symmetricRemainingPairs.isEmpty() && !found) {
                        for (i = 0; i < occurrenceSortedList.size(); i++) {
                            if (occurrenceSortedList.get(i).getKey().equals(rightItem)) {
                                continue;
                            }
                            List<String> rightValue = occurrenceMapDefault.getOrDefault(rightItem, new LinkedList<>());
                            // current test that has most pairs with other tests
                            String tmp = occurrenceSortedList.get(i).getKey();
                            Pair toBeRemoved = new Pair<>(rightItem, tmp);
                            if (rightValue.contains(tmp) && symmetricRemainingPairs.contains(toBeRemoved) && remainingPairs.contains(toBeRemoved) && !order.contains(tmp)) {
                                order.add(rightBorder, tmp);
                                remainingPairs.remove(toBeRemoved);
                                Pair reverseToBeRemoved = new Pair<>(tmp, rightItem);
                                symmetricRemainingPairs.remove(reverseToBeRemoved);
                                symmetricRemainingPairs.remove(toBeRemoved);
                                rightItem = tmp;
                                System.out.println("RIGHTINDEX?: " + tmp);
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!remainingPairs.isEmpty() && !found) {
                        for (i = 0; i < occurrenceSortedList.size(); i++) {
                            if (occurrenceSortedList.get(i).getKey().equals(rightItem)) {
                                continue;
                            }
                            List<String> rightValue = occurrenceMapDefault.getOrDefault(rightItem, new LinkedList<>());
                            // current test that has most pairs with other tests
                            String tmp = occurrenceSortedList.get(i).getKey();
                            Pair toBeRemoved = new Pair<>(rightItem, tmp);
                            if (rightValue.contains(tmp) && remainingPairs.contains(toBeRemoved) && !order.contains(tmp)) {
                                order.add(rightBorder, tmp);
                                remainingPairs.remove(toBeRemoved);
                                rightItem = tmp;
                                System.out.println("RIGHTINDEX??: " + tmp);
                                found = true;
                                break;
                            }
                        }
                    }
                    if (found) {
                        // filled ++;
                        rightBorder ++;
                        System.out.println("new right item: " + rightItem + "; " + (s++));
                    } else {
                        rightEnd = true;
                        if (leftEnd) {
                            int j = 0;
                            if (occurrenceSortedList.size() > 0) {
                                while (order.contains(occurrenceSortedList.get(j).getKey())) {
                                    j++;
                                    if (j == occurrenceSortedList.size()) {
                                        break;
                                    }
                                }
                                if (j != occurrenceSortedList.size()) {
                                    leftEnd = false;
                                    rightEnd = false;
                                    leftItem = occurrenceSortedList.get(j).getKey();
                                    rightItem = occurrenceSortedList.get(j).getKey();
                                    order.add(rightBorder, leftItem);
                                    System.out.println("NEWRIGHTINDEX???: " + leftItem);
                                    System.out.println("BORDER???: " + leftBorder + " " + rightBorder);
                                    leftBorder = rightBorder;
                                    rightBorder = rightBorder + 1;
                                    // filled++;
                                }
                            }
                            if (j == occurrenceSortedList.size() || occurrenceSortedList.size() == 0) {
                                 for (String finalSelectedTest : finalSelectedTests) {
                                    if (!order.contains(finalSelectedTest)) {
                                        order.add(rightBorder, finalSelectedTest);
                                        System.out.println("RIGHTINDEX???: " + finalSelectedTest);
                                        leftItem = finalSelectedTest;
                                        rightItem = finalSelectedTest;
                                        leftBorder = rightBorder;
                                        rightBorder = rightBorder + 1;
                                        leftEnd = false;
                                        rightEnd = false;
                                        // filled ++;
                                        break;
                                    }
                                }
                            }
                            // continue;
                        }
                    }
                    occurrenceMap = new HashedMap();
                    // Set<Pair> tmpPairs = new HashSet<>(remainingPairs);
                    for (Pair pairItem : remainingPairs) {
                        List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
                        valueList.add((String) pairItem.getValue());
                        occurrenceMap.put((String) pairItem.getKey(), valueList);
                        List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
                        keyList.add((String) pairItem.getKey());
                        occurrenceMap.put((String) pairItem.getValue(), keyList);
                    }
                    occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                }
            }
            System.out.println(order.toString());
            orders.add(order);
        }

        System.out.println("FINAL NUM OF ORDERS: " + orders.size());
    }

    private void storeClassesOrdersBasedOnSymmetric() {
        System.out.println("ALLCLASSPAIRS: " + classesPairSet.toString());
        orders = new LinkedList<>();

        List<List<String>> transformedOrders = new LinkedList<>();

        int n = affectedTestClasses.size();
        /* int middle = 0;
        if (n % 2 == 1) {
            middle = (n - 1) / 2;
        } else {
            middle = n / 2;
        } */
        Set<Pair> remainingPairs = new HashSet<>(classesPairSet);
        Set<Pair> symmetricRemainingPairs = new HashSet<>(classesPairSet);

        // deal with the other orders
        while (!remainingPairs.isEmpty()) {
            /* System.out.println("REMAINING PAIRS SIZE: " + remainingPairs.size());
            System.out.println("SEMMETRIC REMAINING PAIRS SIZE: " + symmetricRemainingPairs.size());
            System.out.println("CURRENT ORDER SIZE: " + transformedOrders.size()); */
            Map<String, List<String>> occurrenceMap = new HashedMap();
            // Set<Pair> tmpPairs = new HashSet<>(remainingPairs);
            for (Pair pairItem : remainingPairs) {
                List<String> valueList = occurrenceMap.getOrDefault(pairItem.getKey(), new LinkedList<>());
                valueList.add((String) pairItem.getValue());
                occurrenceMap.put((String) pairItem.getKey(), valueList);
                List<String> keyList = occurrenceMap.getOrDefault(pairItem.getValue(), new LinkedList<>());
                valueList.add((String) pairItem.getKey());
                occurrenceMap.put((String) pairItem.getValue(), keyList);
            }
            List<Map.Entry<String, List<String>>> occurrenceSortedList = new ArrayList<>(occurrenceMap.entrySet());
            // descending order
            Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));

            // System.out.println("PRINT:" + occurrenceSortedList.toString());
            // List<Map.Entry<String, List<String>>> occurrenceSymmetricSortedList = new ArrayList<>(occurrenceSortedList);

            List<String> order = new LinkedList<>();// Arrays.asList(new String[n]);
            order.add(occurrenceSortedList.get(0).getKey());
            // order.set(middle, occurrenceSortedList.get(0).getKey());
            // int left = middle - 1;
            // int right = middle + 1;
            String leftItem = occurrenceSortedList.get(0).getKey();
            String rightItem = occurrenceSortedList.get(0).getKey();
            occurrenceSortedList.remove(0);
            /* List<Map.Entry<String, List<String>>> occurrenceSortedLeftList = new ArrayList<>(occurrenceSortedList);
            occurrenceSortedLeftList.remove(0); */
            int filled = 1;
            int s = 0;
            int leftBorder = 0;
            int rightBorder = 1;
            while (filled < n) {
                boolean leftFound = false;
                int i = 0;
                if (!symmetricRemainingPairs.isEmpty()) {
                    for (i = 0; i < occurrenceSortedList.size(); i++) {
                        if (occurrenceSortedList.get(i).getKey().equals(leftItem)) {
                            continue;
                        }
                        List<String> leftValue = occurrenceMap.getOrDefault(leftItem, new LinkedList<>());
                        // current test that has most pairs with other tests
                        String tmp = occurrenceSortedList.get(i).getKey();
                        Pair toBeRemoved = new Pair<>(tmp, leftItem);
                        if (leftValue.contains(tmp) && symmetricRemainingPairs.contains(toBeRemoved)) {
                            order.add(leftBorder, tmp);
                            remainingPairs.remove(toBeRemoved);
                            symmetricRemainingPairs.remove(toBeRemoved);
                            Pair reverseToBeRemoved = new Pair<>(leftItem, tmp);
                            symmetricRemainingPairs.remove(reverseToBeRemoved);
                            leftItem = tmp;
                            // System.out.println("LEFTINDEX?: " + left);
                            leftFound = true;
                            filled ++;
                            break;
                        }
                    }
                    if (i < occurrenceSortedList.size()) {
                        occurrenceSortedList.remove(i);
                    }
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                } else if (!remainingPairs.isEmpty()) {
                    for (i = 0; i < occurrenceSortedList.size(); i++) {
                        if (occurrenceSortedList.get(i).getKey().equals(leftItem)) {
                            continue;
                        }
                        List<String> leftValue = occurrenceMap.getOrDefault(leftItem, new LinkedList<>());
                        // current test that has most pairs with other tests
                        String tmp = occurrenceSortedList.get(i).getKey();
                        Pair toBeRemoved = new Pair<>(tmp, leftItem);
                        if (leftValue.contains(tmp) && remainingPairs.contains(toBeRemoved)) {
                            order.add(leftBorder, tmp);
                            remainingPairs.remove(new Pair<>(tmp, leftItem));
                            leftItem = tmp;
                            // System.out.println("LEFTINDEX??: " + left);
                            leftFound = true;
                            filled ++;
                            break;
                        }
                    }
                    if (i < occurrenceSortedList.size()) {
                        occurrenceSortedList.remove(i);
                    }
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                }
                if (!leftFound) {
                    /* for (String finalSelectedTest : affectedTestClasses) {
                        if (!order.contains(finalSelectedTest)) {
                            order.set(left, finalSelectedTest);
                            // System.out.println("LEFTINDEX???: " + left);
                            leftItem = finalSelectedTest;
                            break;
                        }
                    } */
                }
                // System.out.println("new left item: " + leftItem + "; " + (s++));
                int j = 0;
                boolean rightFound = false;
                if (!symmetricRemainingPairs.isEmpty()) {
                    for (j = 0; j < occurrenceSortedList.size(); j++) {
                        if (occurrenceSortedList.get(j).getKey().equals(rightItem)) {
                            continue;
                        }
                        List<String> rightValue = occurrenceMap.getOrDefault(rightItem, new LinkedList<>());
                        // current test that has most pairs with other tests
                        String tmp = occurrenceSortedList.get(j).getKey();
                        Pair toBeRemoved = new Pair<>(rightItem, tmp);
                        if (rightValue.contains(tmp) && symmetricRemainingPairs.contains(toBeRemoved)) {
                            order.add(rightBorder, tmp);
                            remainingPairs.remove(toBeRemoved);
                            Pair reverseToBeRemoved = new Pair<>(tmp, rightItem);
                            symmetricRemainingPairs.remove(reverseToBeRemoved);
                            symmetricRemainingPairs.remove(toBeRemoved);
                            rightItem = tmp;
                            // System.out.println("RIGHTINDEX?: " + right);
                            rightBorder ++;
                            rightFound = true;
                            break;
                        }
                    }
                    if (j < occurrenceSortedList.size()) {
                        occurrenceSortedList.remove(j);
                    }
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                } else if (!remainingPairs.isEmpty()) {
                    for (j = 0; j < occurrenceSortedList.size(); j++) {
                        if (occurrenceSortedList.get(j).getKey().equals(rightItem)) {
                            continue;
                        }
                        List<String> rightValue = occurrenceMap.getOrDefault(rightItem, new LinkedList<>());
                        // current test that has most pairs with other tests
                        String tmp = occurrenceSortedList.get(j).getKey();
                        Pair toBeRemoved = new Pair<>(rightItem, tmp);
                        if (rightValue.contains(tmp) && remainingPairs.contains(toBeRemoved)) {
                            order.add(rightBorder, tmp);
                            remainingPairs.remove(toBeRemoved);
                            rightItem = tmp;
                            // System.out.println("RIGHTINDEX??: " + right);
                            rightBorder++;
                            rightFound = true;
                            break;
                        }
                    }
                    if (j < occurrenceSortedList.size()) {
                        occurrenceSortedList.remove(j);
                    }
                    Collections.sort(occurrenceSortedList, (o1, o2) -> (o2.getValue().size() - o1.getValue().size()));
                }
                if (!rightFound) {
                    /* for (String finalSelectedTest : affectedTestClasses) {
                        if (!order.contains(finalSelectedTest)) {
                            order.set(right, finalSelectedTest);
                            // System.out.println("RIGHTINDEX???: " + right);
                            rightItem = finalSelectedTest;
                            right ++;
                            break;
                        }
                    }*/
                }
                // System.out.println("new right item: " + rightItem + "; " + (s++));
            }
            System.out.println(order.toString());
            transformedOrders.add(order);
        }

        System.out.println("FINAL NUM OF ORDERS: " + transformedOrders.size());
    }

    private void storeOrdersByClasses() {
        System.out.println("ALLCLASSPAIRS: " + classesPairSet.toString());
        for (Pair classPair: classesPairSet) {
            System.out.println("(" + classPair.getKey() + ", " + classPair.getValue() + ")");
        }
        orders = new LinkedList<>();

        List<String> affectedTestClassesList = new LinkedList<>();
        for (String affectedTestClass : affectedTestClasses) {
            System.out.println(affectedTestClass);
            affectedTestClassesList.add(affectedTestClass);
        }
        System.out.println("CLASS SIZE: " + affectedTestClassesList.size());

        Map<String, List<String>> testClassesToTests = new HashMap<>();
        for (String testItem : allTestMethods) {
            String testItemClass = testItem.substring(0, testItem.lastIndexOf("."));
            System.out.println("testItemClass: " + testItemClass);
            List<String> testItemValue = testClassesToTests.getOrDefault(testItemClass, new LinkedList<>());
            testItemValue.add(testItem);
            testClassesToTests.put(testItemClass, testItemValue);
        }
        System.out.println("TOTAL TEST CLASS SIZE: " + testClassesToTests.keySet().size());

        // obtain the TuscanSquare for the size of tests
        int n = affectedTestClasses.size();
        generateTuscanSquare(n);
        Set<Pair> remainingClassesPairs = new HashSet<>(classesPairSet);

        // transfer the TuscanSquare to be actual orders
        List<List<String>> transformedOrders = new LinkedList<>();
        for (int[] ri : r) {
            List<String> oneOrder = new LinkedList<>();
            for (int index = 0; index < ri.length - 1; index ++) {
                oneOrder.add(affectedTestClassesList.get(ri[index]));
            }
            transformedOrders.add(oneOrder);
        }

        // deal with the other orders
        while (!remainingClassesPairs.isEmpty()) {
            int maxAdditionalSize = 0;
            int initialSize = remainingClassesPairs.size();
            System.out.println("INITIAL SIZE: " + initialSize);
            int maxIndex = 0;
            for (int i = 0 ; i < transformedOrders.size() ; i++) {
                List<String> orderItem = transformedOrders.get(i);
                Set<Pair> finalRemainingPairs = new HashSet<>(remainingClassesPairs);
                for (int j = 0 ; j < orderItem.size() - 1 ; j++) {
                    Pair toBeRemoved = new Pair<>(orderItem.get(j), orderItem.get(j + 1));
                    finalRemainingPairs.remove(toBeRemoved);
                }
                int finalSize = finalRemainingPairs.size();
                // System.out.println("FINAL SIZE: " + finalSize);
                if (initialSize - finalSize > maxAdditionalSize) {
                    maxAdditionalSize = initialSize - finalSize;
                    maxIndex = i;
                    // System.out.println("maxAdditionalSize(change to): " + maxAdditionalSize);
                }
            }
            List<String> maxClassesOrder = transformedOrders.get(maxIndex);
            System.out.println("maxClassesOrder: " + maxClassesOrder.toString());
            List<String> maxOrder = new LinkedList<>();
            for (String maxOrderItem : maxClassesOrder) {
                System.out.println("maxOrderItem: " + maxOrderItem);
                maxOrder.addAll(testClassesToTests.get(maxOrderItem));
            }
            orders.add(maxOrder);
            for (int k = 0 ; k < maxClassesOrder.size() - 1 ; k++) {
                Pair toBeRemoved = new Pair<>(maxClassesOrder.get(k), maxClassesOrder.get(k + 1));
                remainingClassesPairs.remove(toBeRemoved);
            }
            System.out.println("finalMaxAdditionalSize(change to): " + maxAdditionalSize);
            // System.out.println("finalOrder: " + maxOrder.toString());
            transformedOrders.remove(maxIndex);
        }

        System.out.println("FINAL NUM OF ORDERS: " + orders.size());
    }

    private Set<String> getSelectedTests() {
        Path path;
        if (isEkstazi) {
            path = ekstaziSelectedTestsPath;
        } else {
            path = startsSelectedTestsPath;
        }
        selectedTests = new HashSet<>();
        try {
            BufferedReader in = Files.newBufferedReader(path, StandardCharsets.UTF_8);
            String str;
            while ((str = in.readLine()) != null) {
                selectedTests.add(str);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return selectedTests;
    }

    private void getTransitiveClosure() {
        if (isEkstazi) {
            try {
                File ekstaziDirFile = new File(RTSDir);
                File[] files = ekstaziDirFile.listFiles();
                for (File file : files) {
                    String fileName = file.toString().substring(file.toString().lastIndexOf(File.separator) + 1);
                    if (fileName.endsWith(".clz")) {
                        String transitiveClosureKey = fileName.substring(0, fileName.indexOf(".clz"));
                        BufferedReader in = Files.newBufferedReader(Paths.get(file.toString()), StandardCharsets.UTF_8);
                        String str;
                        Set<String> transitiveClosureValue = new HashSet<>();
                        while ((str = in.readLine()) != null) {
                            if (!str.contains(".class") || !str.startsWith("file:")) {
                                continue;
                            }
                            int sepIndex = str.lastIndexOf("_");
                            String urlExternalForm = str.substring(0, sepIndex);
                            URL url = new URL(urlExternalForm);
                            String transitiveClosureValueArrayItem = getClassNameFromClassFile(url.getPath());
                            transitiveClosureValue.add(transitiveClosureValueArrayItem);
                        }
                        transitiveClosure.put(transitiveClosureKey, transitiveClosureValue);
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
            // the dependency map from classes to their dependencies (test classes)
            reverseTransitiveClosure = getReverseClosure(transitiveClosure);
        } else {
            try {
                List<String> zlcLines = Files.readAllLines(startsDependenciesPath, Charset.defaultCharset());
                String firstLine = zlcLines.get(0);
                String space = " ";

                // check whether the first line is for *
                if (firstLine.startsWith(STAR_FILE) || firstLine.equals("PLAIN_TEXT")) {
                    zlcLines.remove(0);
                }

                for (String line : zlcLines) {
                    String[] parts = line.split(space);
                    String stringURL = parts[0];
                    Set<String> tests = parts.length == 3 ? fromCSV(parts[2]) : new HashSet<String>();
                    URL url = new URL(stringURL);
                    String reverseTransitiveClosureKey = getClassNameFromClassFile(url.getPath());
                    reverseTransitiveClosure.put(reverseTransitiveClosureKey, tests);
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
            // the dependency map from test classes to their dependencies (classes)
            transitiveClosure = getReverseClosure(reverseTransitiveClosure);
        }
    }

    // apply the same logic as STARTS for Ekstazi
    private void checkSelectAll() throws IOException, MojoExecutionException {
        String cpString = Writer.pathToString(sureFireClassPath.getClassPath());
        List<String> sfPathElements = getCleanClassPath(cpString);

        selectAll = false;
        if (!isSameClassPath(sfPathElements) || !hasSameJarChecksum(sfPathElements)) {
            // Force retestAll because classpath changed since last run
            // don't compute changed and non-affected classes
            // Make nonAffected empty so dependencies can be updated
            Writer.writeClassPath(cpString, artifactsDir);
            writeJarChecksums(sfPathElements, artifactsDir, jarCheckSums);
            selectAll = true;
        }
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

        selectMore = Configuration.config().getProperty("dt.incdetector.selectmore", false);
        selectAll = false;
        detectOrNot = Configuration.config().getProperty("dt.incdetector.detectornot", true);
        isEkstazi = Configuration.config().getProperty("dt.incdetector.ekstazi", false);
        artifactsDir = getArtifactsDir();
        RTSDir = getRTSDir();
        ekstaziSelectedTestsPath = relativePath(PathManager.ekstaziPath(), Paths.get("selected-tests"));
        startsSelectedTestsPath = relativePath(PathManager.startsPath(), Paths.get("selected-tests"));
        startsDependenciesPath = relativePath(PathManager.startsPath(), Paths.get("deps.zlc"));

        transitiveClosure = new HashMap<>();
        reverseTransitiveClosure = new HashMap<>();

        getSureFireClassPath(project);
        loader = createClassLoader(sureFireClassPath);
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

    private String getRTSDir() throws FileNotFoundException {
        if (RTSDir == null) {
            if (isEkstazi) {
                RTSDir = PathManager.ekstaziPath().toString();
            } else {
                RTSDir = PathManager.startsPath().toString();
            }
            File file = new File(RTSDir);
            if (!file.mkdirs() && !file.exists()) {
                throw new FileNotFoundException("I could not create artifacts dir: " + RTSDir);
            }
        }
        return RTSDir;
    }

    private List<String> getCleanClassPath(String cp) {
        List<String> cpPaths = new ArrayList<>();
        String[] paths = cp.split(File.pathSeparator);
        String classes = File.separator + TARGET + File.separator + CLASSES;
        String testClasses = File.separator + TARGET + File.separator + TEST_CLASSES;
        Set<String> classPathSet = new HashSet<>();
        for (int i = 0; i < paths.length; i++) {
            paths[i].replaceAll(" ", "");
            // TODO: should we also exclude SNAPSHOTS from same project?
            if (paths[i].contains(classes) || paths[i].contains(testClasses)) {
                continue;
            }
            classPathSet.add(paths[i]);
        }
        for (String classPath : classPathSet) {
            cpPaths.add(classPath);
        }
        return cpPaths;
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

    @Override
    protected List<String> getTests(
            final MavenProject project,
            TestFramework testFramework) throws IOException {
        List<String> tests = getOriginalOrder(project, testFramework, true);
        List<String> affectedTests = new ArrayList<>();

        String delimiter = testFramework.getDelimiter();
        for (String test : tests) {
            String clazz = test.substring(0, test.lastIndexOf(delimiter));
            if (affectedTestClasses.contains(clazz)) {
                affectedTests.add(test);
            }
        }
        return affectedTests;
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

    private boolean hasSameJarChecksum(List<String> cleanSfClassPath) throws FileNotFoundException {
        if (cleanSfClassPath.isEmpty()) {
            return true;
        }
        String oldChecksumPathFileName = Paths.get(getArtifactsDir(), JAR_CHECKSUMS).toString();
        if (!new File(oldChecksumPathFileName).exists()) {
            return false;
        }
        boolean noException = true;
        try {
            List<String> lines = Files.readAllLines(Paths.get(oldChecksumPathFileName));
            Map<String, String> checksumMap = new HashMap<>();
            for (String line : lines) {
                String[] elems = line.split(EQUAL);
                checksumMap.put(elems[0], elems[1]);
            }
            jarCheckSums = new ArrayList<>();
            for (String path : cleanSfClassPath) {
                Pair<String, String> pair = getJarToChecksumMapping(path);
                jarCheckSums.add(pair);
                String oldCS = checksumMap.get(pair.getKey());
                noException &= pair.getValue().equals(oldCS);
            }
        } catch (IOException ioe) {
            noException = false;
            // reset to null because we don't know what/when exception happened
            jarCheckSums = null;
            ioe.printStackTrace();
        }
        return noException;
    }

    private boolean isSameClassPath(List<String> sfPathString) throws MojoExecutionException, FileNotFoundException {
        if (sfPathString.isEmpty()) {
            return true;
        }
        String oldSfPathFileName = Paths.get(getArtifactsDir(), SF_CLASSPATH).toString();
        if (!new File(oldSfPathFileName).exists()) {
            return false;
        }
        try {
            List<String> oldClassPathLines = Files.readAllLines(Paths.get(oldSfPathFileName));
            if (oldClassPathLines.size() != 1) {
                throw new MojoExecutionException(SF_CLASSPATH + " is corrupt! Expected only 1 line.");
                // This exception is not correct and need to be modified.
            }
            List<String> oldClassPathelements = getCleanClassPath(oldClassPathLines.get(0));
            // comparing lists and not sets in case order changes
            if (sfPathString.equals(oldClassPathelements)) {
                return true;
            }
            Set<String> sfPathStringSet = new HashSet<>();
            sfPathStringSet.addAll(sfPathString);
            Set<String> oldClassPathelementsSet = new HashSet<>();
            oldClassPathelementsSet.addAll(sfPathString);
            if (sfPathStringSet.equals(oldClassPathelementsSet)) {
                return true;
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
        return false;
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

    private void writeJarChecksums(List<String> sfPathString, String artifactsDir, List<Pair> jarCheckSums) {
        String outFilename = Paths.get(artifactsDir, JAR_CHECKSUMS).toString();
        try (BufferedWriter writer = Writer.getWriter(outFilename)) {
            if (jarCheckSums != null) {
                // we already computed the checksums while checking with old version in RunMojo#hasSameJarChecksum()
                for (Pair<String, String> pair : jarCheckSums) {
                    writer.write(pair.toString());
                    writer.write(System.lineSeparator());
                }
            } else {
                for (String path : sfPathString) {
                    if (path.isEmpty()) {
                        continue;
                    }
                    writer.write(getJarToChecksumMapping(path).toString());
                    writer.write(System.lineSeparator());
                }
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    private static Set<String> fromCSV(String tests) {
        return new HashSet<>(Arrays.asList(tests.split(",")));
    }

    public static String getClassNameFromClassFile(String filePath) {
        try {
            byte[] classFileBuffer = Files.readAllBytes(Paths.get(filePath));
            ClassReader classReader = new ClassReader(classFileBuffer);
            return classReader.getClassName().replaceAll("/", ".");
        } catch (IOException e) {
            e.printStackTrace();
        }
        return "";
    }

    private static void helper(int[] a, int i) {
        System.arraycopy(a, 0, r[i], 0, a.length);
    }

    private static void generateTuscanSquare(int n) {
        int nn = n;
        while((n-1) % 4 == 0 && n != 1 && n != 9) n = (n-1)/2+1;

        r = new int[nn][];
        for (int i = 0; i < nn; i++) {
            r[i] = new int[nn+1];
        }

        if (n % 2 == 0) {
            // https://mathoverflow.net/questions/60856/hamilton-paths-in-k-2n/60859#60859
            int[] a = new int[n];
            for (int i = 0; i < n; i += 2) {
                a[i] = i / 2;
                a[i+1] = n - 1 - a[i];
            }
            helper(a, 0);
            for (int j = 1; j < n; j++) {
                for (int i = 0; i < n; i++) {
                    a[i] = (a[i] + 1) % n;
                }
                helper(a, j);
            }
        } else if (n % 4 == 3) {
            int k = (n - 3) / 4;
            int[] b = new int[n];
            for (int i = 0; i < n - 1; i++) {
                int p = (i == 0) ? 1 :
                        ((i == k + 1) ? 4*k + 2 :
                                ((i == 2*k + 2) ? 3 :
                                        ((i == 3*k + 2) ? 4*k : 2*k)));
                int[] a = new int[n];
                for (int j = 0; j < n; j++) {
                    a[(j < p) ? n+j-p : j-p] = (j == 0) ? (n - 1) : (i + ((j % 2 == 0) ? (j / 2) : (n - 1 - (j - 1) / 2))) % (n - 1);
                }
                b[a[n-1]] = a[0];
                helper(a, i);
            }
            int[] t = new int[n];
            t[0] = n - 1;
            for (int i = 1; i < n; i++) {
                t[i] = b[t[i-1]];
            }
            helper(t, n-1);
        } else if (n == 9) {
            int[][] t = {{0,1,7,2,6,3,5,4,8},
                    {3,7,4,6,5,8,1,2,0},
                    {1,4,0,5,7,6,8,2,3},
                    {6,0,7,8,3,4,2,5,1},
                    {2,7,1,0,8,4,5,3,6},
                    {7,3,0,2,1,8,5,6,4},
                    {5,0,4,1,3,2,8,6,7},
                    {4,3,8,7,0,6,1,5,2},
                    {8,0,3,1,6,2,4,7,5}};
            for (int i = 0; i < 9; i++) {
                helper(t[i], i);
            }
        }
        else assert(false);

        while (nn != n){
            // n + 1 == 4*m - 2
            // https://www.sciencedirect.com/science/article/pii/0095895680900441

            n = n * 2 - 1;

            int h = (n + 1) / 2;

            for (int i = 0; i < h; i++) {
                for (int j = 0; j < h; j++) {
                    r[i][n-j] = r[i][j] + h;
                }
            }
            for (int i = h; i < n; i++) {
                /*
                for (int j = 0; j < n+1; j++) {
                    r[i][j] = ((j % 2 == 0) ? 0 : h) + (i-h + ((j % 2 == 0) ? (j / 2) : (n - (j - 1) / 2))) % h;
                }
                */
                for (int j = 0; j < h - 1; j++) {
                    r[i][j] = ((j % 2 == 0) ? 0 : h) + (i-h + ((j % 2 == 0) ? (j / 2) : (h - 2 - (j - 1) / 2))) % (h - 1);
                }
                r[i][h-1] = h-1;
                for (int j = h; j < n + 1; j++) {
                    r[i][j] = ((j % 2 == 0) ? 0 : h) + r[i][j-h] % h;
                }
            }
            for (int i = 0; i < n; i++) {
                int l = 0;
                for (; l < n; l++) {
                    if (r[i][l] == n) break;
                }
                int[] t = new int[n];
                System.arraycopy(r[i], l+1, t, 0, n-l);
                System.arraycopy(r[i], 0, t, n-l, l);

                System.arraycopy(t, 0, r[i], 0, n);
            }
        }
    }
}
