package edu.illinois.cs.dt.tools.plugin;

import edu.illinois.cs.dt.tools.utility.ErrorLogger;
import edu.illinois.cs.dt.tools.utility.Level;
import edu.illinois.cs.dt.tools.utility.Logger;
import edu.illinois.cs.dt.tools.utility.PathManager;
import edu.illinois.cs.dt.tools.utility.SootAnalysis;
import edu.illinois.cs.testrunner.configuration.Configuration;
import edu.illinois.cs.testrunner.data.framework.TestFramework;
import edu.illinois.starts.data.ZLCFormat;
import edu.illinois.starts.enums.DependencyFormat;
import edu.illinois.starts.helpers.Writer;
import edu.illinois.starts.maven.AgentLoader;
import edu.illinois.starts.util.Pair;
import org.apache.maven.artifact.DependencyResolutionRequiredException;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.plugins.annotations.ResolutionScope;
import org.apache.maven.project.MavenProject;
import org.apache.maven.surefire.booter.Classpath;
import org.apache.maven.surefire.booter.SurefireExecutionException;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.illinois.starts.constants.StartsConstants.CLASSES;
import static edu.illinois.starts.constants.StartsConstants.COMMA;
import static edu.illinois.starts.constants.StartsConstants.TRUE;
import static edu.illinois.starts.constants.StartsConstants.FALSE;
import static edu.illinois.starts.constants.StartsConstants.JAR_CHECKSUMS;
import static edu.illinois.starts.constants.StartsConstants.SF_CLASSPATH;
import static edu.illinois.starts.constants.StartsConstants.STARTS_EXCLUDE_PROPERTY;
import static edu.illinois.starts.constants.StartsConstants.TEST_CLASSES;

@Mojo(name = "incdetect", defaultPhase = LifecyclePhase.TEST, requiresDependencyResolution = ResolutionScope.TEST)
public class IncDetectorMojo extends DetectorMojo {
    /**
     * The directory in which to store STARTS artifacts that are needed between runs.
     */
    protected String artifactsDir;

    protected ClassLoader loader;

    /**
     * Set this to "false" to disable smart hashing, i.e., to *not* strip
     * Bytecode files of debug info prior to computing checksums. See the "Smart
     * Checksums" Sections in the Ekstazi paper:
     * http://dl.acm.org/citation.cfm?id=2771784
     */
    @Parameter(property = "cleanBytes", defaultValue = TRUE)
    protected boolean cleanBytes;

    /**
     * Allows to switch the format in which we want to store the test dependencies.
     * A full list of what we currently support can be found in
     * @see edu.illinois.starts.enums.DependencyFormat
     */
    @Parameter(property = "depFormat", defaultValue = "ZLC")
    protected DependencyFormat depFormat;

    /**
     * Set this to "false" to not filter out "sun.*" and "java.*" classes from jdeps parsing.
     */
    @Parameter(property = "filterLib", defaultValue = TRUE)
    protected boolean filterLib;

    /**
     * Path to directory that contains the result of running jdeps on third-party
     * and standard library jars that an application may need, e.g., those in M2_REPO.
     */
    @Parameter(property = "gCache", defaultValue = "${basedir}${file.separator}jdeps-cache")
    protected String graphCache;

    /**
     * Output filename for the graph, if printGraph == true.
     */
    @Parameter(defaultValue = "graph", readonly = true, required = true)
    protected String graphFile;

    protected List<Pair> jarCheckSums = null;

    protected Set<String> nonAffectedTests;

    /**
     * Set this to "false" to not print the graph obtained from jdeps parsing.
     * When "true" the graph is written to file after the run.
     */
    @Parameter(property = "printGraph", defaultValue = TRUE)
    protected boolean printGraph;

    private Classpath sureFireClassPath;

    private static final String TARGET = "target";
    /**
     * Set this to "false" to not add jdeps edges from 3rd party-libraries.
     */
    @Parameter(property = "useThirdParty", defaultValue = FALSE)
    protected boolean useThirdParty;

    /**
     * Set this to "true" to update test dependencies on disk. The default value of
     * "false" is useful for "dry runs" where one may want to see the affected
     * tests, without updating test dependencies.
     */
    @Parameter(property = "updateChecksums", defaultValue = FALSE)
    private boolean updateChecksums;

    /**
     * Format of the ZLC dependency file deps.zlc
     * Set to "INDEXED" to store indices of tests
     * Set to "PLAIN_TEXT" to store full URLs of tests
     */
    @Parameter(property = "zlcFormat", defaultValue = "PLAIN_TEXT")
    protected ZLCFormat zlcFormat;

    protected boolean selectMore;

    protected boolean selectBasedOnMethodsCall;

    protected boolean selectBasedOnMethodsCallUpgrade;

    protected boolean removeBasedOnMethodsCall;

    protected boolean fineGranularity;

    protected boolean detectOrNot;

    protected int distance;

    protected String ekstaziSelectedTestsFile;

    protected String ekstaziDependenciesFile;

    protected String startsSelectedTestsFile;

    protected String startsDependenciesFile;

    protected boolean isEkstazi;

    private Set<String> affectedTestClasses;

    protected List<String> selectedTests;

    private static Set<String> immutableList;

    @Override
    public void execute() {
        superExecute();

        final ErrorLogger logger = new ErrorLogger();
        this.outputPath = PathManager.detectionResults();
        this.coordinates = mavenProject.getGroupId() + ":" + mavenProject.getArtifactId() + ":" + mavenProject.getVersion();

        logger.runAndLogError(() -> defineSettings(logger, mavenProject));

        long startTime = System.currentTimeMillis();
        try {
            affectedTestClasses = computeAffectedTests(mavenProject);
            if (!detectOrNot) {
                System.out.println("Not detect flaky tests at the first run");
                return;
            }
        } catch (IOException e) {
            e.printStackTrace();
        } catch (MojoExecutionException e) {
            e.printStackTrace();
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
        timing(startTime);

        startTime = System.currentTimeMillis();
        logger.runAndLogError(() -> detectorExecute(logger, mavenProject, moduleRounds(coordinates)));
        timing(startTime);
    }

    // from SelectMojo
    private Set<String> computeAffectedTests(final MavenProject project) throws IOException, MojoExecutionException, ClassNotFoundException {
        if (isEkstazi) {
            return computeEkstaziAffectedTests(project);
        }

        String cpString = Writer.pathToString(sureFireClassPath.getClassPath());

        Set<String> affectedTests = new HashSet<>();

        if (!detectOrNot) {
            return affectedTests;
        }

        try {
            BufferedReader in = new BufferedReader(new FileReader(startsSelectedTestsFile));
            String str;
            while ((str = in.readLine()) != null) {
                affectedTests.add(str);
            }
        } catch (IOException e) {
        }

        if (!selectMore) {
            return affectedTests;
        }

        Map<String, Set<String>> reverseTransitiveClosure = new HashMap<>();

        try {
            BufferedReader in = new BufferedReader(new FileReader(startsDependenciesFile));
            String str;
            while ((str = in.readLine()) != null) {
                if (!str.contains(",")) {
                    continue;
                }
                String transitiveClosureKey = str.substring(0, str.indexOf(","));
                String transitiveClosureValues = str.substring(str.indexOf(","));
                String[] transitiveClosureValueArray = transitiveClosureValues.split(",");
                Set<String> transitiveClosureValue = new HashSet<>();
                for (String transitiveClosureValueArrayItem: transitiveClosureValueArray) {
                    transitiveClosureValue.add(transitiveClosureValueArrayItem);
                }
                reverseTransitiveClosure.put(transitiveClosureKey, transitiveClosureValue);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        // the dependency map from classes to their dependencies
        Map<String, Set<String>> transitiveClosure = getReverseClosure(reverseTransitiveClosure);

        Set<String> additionalTests = new HashSet<>();

        // iter through the affected tests and find what depends on
        Set<String> processedClasses = new HashSet<>();

        // iter through the affected tests and find what depends on
        Set<String> affectedClasses = new HashSet<>();

        // TODO: not checked yet
        if (selectBasedOnMethodsCall) {
            Map<String, List<String>> testClassToMethod = new HashMap<>();
            List<String> currentTests = super.getTests(project, getTestFramework());

            String delimiter = getTestFramework().getDelimiter();
            for (String test : currentTests) {
                String className = test.substring(0, test.lastIndexOf(delimiter));
                if (!testClassToMethod.containsKey(className)) {
                    testClassToMethod.put(className, new ArrayList<>());
                }
                testClassToMethod.get(className).add(test);
            }

            Map<String, Set<String>> SootAnalysisTestClassesToClassesSet = new HashMap<>();
            for (String testClass : testClassToMethod.keySet()) {
                if(affectedTests.contains(testClass)) {
                    Set<String> sootNewAffectedClasses = new HashSet<>();
                    sootNewAffectedClasses = SootAnalysis.analysis(cpString, testClass, testClassToMethod);

                    affectedClasses.addAll(sootNewAffectedClasses);
                    SootAnalysisTestClassesToClassesSet.put(testClass, sootNewAffectedClasses);
                }
            }

            for (String affectedClass : affectedClasses) {
                if (reverseTransitiveClosure.containsKey(affectedClass)) {
                    Set<String> additionalAffectedTestClasses = reverseTransitiveClosure.get(affectedClass);
                    for (String additionalAffectedTestClass : additionalAffectedTestClasses) {
                        if(selectBasedOnMethodsCallUpgrade) {
                            Set<String> reachableClassesFromAdditionalAffectedTestClass = new HashSet<>();
                            if(SootAnalysisTestClassesToClassesSet.containsKey(additionalAffectedTestClass)) {
                                reachableClassesFromAdditionalAffectedTestClass = SootAnalysisTestClassesToClassesSet.get(additionalAffectedTestClass);
                            }
                            else {
                                reachableClassesFromAdditionalAffectedTestClass = SootAnalysis.analysis(cpString, additionalAffectedTestClass, testClassToMethod);
                                SootAnalysisTestClassesToClassesSet.put(additionalAffectedTestClass, reachableClassesFromAdditionalAffectedTestClass);
                            }
                            if (reachableClassesFromAdditionalAffectedTestClass.contains(affectedClass)) {
                                additionalTests.add(additionalAffectedTestClass);
                            }
                        }
                        else {
                            additionalTests.add(additionalAffectedTestClass);
                        }
                    }
                }
            }
            affectedTests.addAll(additionalTests);
            return affectedTests;
        }

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
                Set<String> dest = new HashSet<>();
                dest.add(dependency);
                try {
                    Class clazz = loader.loadClass(dependency);
                    for (Field field : clazz.getDeclaredFields()) {
                        if (inImmutableList(field) && Modifier.isFinal(field.getModifiers())) {
                            continue;
                        }
                        if (Modifier.isStatic(field.getModifiers())) {
                            String upperLevelAffectedClass = clazz.getName();
                            Set<String> upperLevelAffectedTestClasses = reverseTransitiveClosure.get(upperLevelAffectedClass);
                            if (upperLevelAffectedTestClasses != null) {
                                for (String upperLevelAffectedTestClass: upperLevelAffectedTestClasses) {
                                    additionalTests.add(upperLevelAffectedTestClass);
                                }
                            }
                            break;
                        }
                    }
                    processedClasses.add(dependency);
                } catch (ClassNotFoundException CNFE)  {
                    // System.out.println("Can not load class. Test dependency skipping: " + dependency);
                } catch (NoClassDefFoundError NCDFE)  {
                    // System.out.println("Can not load class. Test dependency skipping: " + dependency);
                }

            }
        }

        affectedTests.addAll(additionalTests);
        return affectedTests;
    }

    private Set<String> computeEkstaziAffectedTests(final MavenProject project) throws IOException, MojoExecutionException, ClassNotFoundException {
        String cpString = Writer.pathToString(sureFireClassPath.getClassPath());
        List<String> sfPathElements = getCleanClassPath(cpString);

        Set<String> allTests = new HashSet<>(getTestClasses(project, getTestFramework()));
        Set<String> affectedTests = new HashSet<>();

        boolean selectAll = false;
        if (!isSameClassPath(sfPathElements) || !hasSameJarChecksum(sfPathElements)) {
            // Force retestAll because classpath changed since last run
            // don't compute changed and non-affected classes
            dynamicallyUpdateExcludes(new ArrayList<String>());
            // Make nonAffected empty so dependencies can be updated
            nonAffectedTests = new HashSet<>();
            Writer.writeClassPath(cpString, artifactsDir);
            Writer.writeJarChecksums(sfPathElements, artifactsDir, jarCheckSums);
            selectAll = true;
        }

        if (selectAll) {
            return allTests;
        }

        try {
            BufferedReader in = new BufferedReader(new FileReader(ekstaziSelectedTestsFile));
            String str;
            while ((str = in.readLine()) != null) {
                affectedTests.add(str);
            }
        } catch (IOException e) {
        }

        if (!selectMore) {
            return affectedTests;
        }

        Map<String, Set<String>> transitiveClosure = new HashMap<>();

        try {
            BufferedReader in = new BufferedReader(new FileReader(ekstaziDependenciesFile));
            String str;
            while ((str = in.readLine()) != null) {
                if (!str.contains(",")) {
                    continue;
                }
                String transitiveClosureKey = str.substring(0, str.indexOf(","));
                String transitiveClosureValues = str.substring(str.indexOf(","));
                String[] transitiveClosureValueArray = transitiveClosureValues.split(",");
                Set<String> transitiveClosureValue = new HashSet<>();
                for (String transitiveClosureValueArrayItem: transitiveClosureValueArray) {
                    transitiveClosureValue.add(transitiveClosureValueArrayItem);
                }
                transitiveClosure.put(transitiveClosureKey, transitiveClosureValue);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        // the dependency map from classes to their dependencies
        Map<String, Set<String>> reverseTransitiveClosure = getReverseClosure(transitiveClosure);

        Set<String> additionalTests = new HashSet<>();

        // iter through the affected tests and find what depends on
        Set<String> processedClasses = new HashSet<>();

        // add class count for basic version ...
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
                        if (inImmutableList(field) && Modifier.isFinal(field.getModifiers())) {
                            continue;
                        }
                        if (Modifier.isStatic(field.getModifiers())) {
                            String upperLevelAffectedClass = clazz.getName();
                            Set<String> upperLevelAffectedTestClasses = reverseTransitiveClosure.get(upperLevelAffectedClass);
                            if (upperLevelAffectedTestClasses != null) {
                                for (String upperLevelAffectedTestClass: upperLevelAffectedTestClasses) {
                                    additionalTests.add(upperLevelAffectedTestClass);
                                }
                            }
                            break;
                        }
                    }
                    processedClasses.add(dependency);
                } catch (ClassNotFoundException CNFE)  {
                } catch (NoClassDefFoundError NCDFE)  {
                }
            }
        }

        affectedTests.addAll(additionalTests);
        return affectedTests;
    }

    public ClassLoader createClassLoader(Classpath sfClassPath) {
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

    @Override
    protected Void defineSettings(final ErrorLogger logger, final MavenProject project) throws IOException {
        super.defineSettings(logger, project);

        artifactsDir = getArtifactsDir();
        cleanBytes = true;
        depFormat = DependencyFormat.ZLC;
        filterLib = true;
        graphFile = "graph";
        graphCache = "jdeps-cache";
        printGraph = true;
        updateChecksums = true;
        useThirdParty = false;
        zlcFormat = ZLCFormat.PLAIN_TEXT;
        selectMore = Configuration.config().getProperty("dt.incdetector.selectmore", false);
        selectBasedOnMethodsCall = Configuration.config().getProperty("dt.incdetector.selectonmethods", false);
        selectBasedOnMethodsCallUpgrade = Configuration.config().getProperty("dt.incdetector.selectonmethodsupgrade", false);
        removeBasedOnMethodsCall = Configuration.config().getProperty("dt.incdetector.removeonmethods", false);
        detectOrNot = Configuration.config().getProperty("dt.incdetector.detectornot", true);
        fineGranularity = Configuration.config().getProperty("dt.incdetector.finegranularity", false);
        distance = Configuration.config().getProperty("dt.incdetector.distance", Integer.MAX_VALUE);
        isEkstazi = Configuration.config().getProperty("dt.incdetector.ekstazi", false);
        ekstaziSelectedTestsFile = Configuration.config().getProperty("dt.incdetector.ekstaziselectedtests", "");
        ekstaziDependenciesFile = Configuration.config().getProperty("dt.incdetector.ekstazidependencies", "");;
        startsSelectedTestsFile = Configuration.config().getProperty("dt.incdetector.startsselectedtests", "");
        startsDependenciesFile = Configuration.config().getProperty("dt.incdetector.startsdependencies", "");;

        getSureFireClassPath(project);
        loader = createClassLoader(sureFireClassPath);

        return null;
    }

    private void dynamicallyUpdateExcludes(List<String> excludePaths) throws MojoExecutionException {
        if (AgentLoader.loadDynamicAgent()) {
            System.setProperty(STARTS_EXCLUDE_PROPERTY, Arrays.toString(excludePaths.toArray(new String[0])));
        } else {
            throw new MojoExecutionException("I COULD NOT ATTACH THE AGENT");
        }
    }

    public String getArtifactsDir() throws FileNotFoundException {
        if (artifactsDir == null) {
            artifactsDir = PathManager.cachePath().toString();
            File file = new File(artifactsDir);
            if (!file.mkdirs() && !file.exists()) {
                throw new FileNotFoundException("I could not create artifacts dir: " + artifactsDir);
            }
        }
        return artifactsDir;
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
        for(String classPath: classPathSet) {
            cpPaths.add(classPath);
        }
        return cpPaths;
    }

    public Map<String, Set<String>> getReverseClosure(Map<String, Set<String>> transitiveClosure) {
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

    public Classpath getSureFireClassPath(final MavenProject project) {
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

    protected List<String> getTests(
            final MavenProject project,
            TestFramework testFramework) throws IOException {
        List<String> tests;
        if (fineGranularity && this.selectedTests != null) {
            tests = this.selectedTests;
        } else {
            tests = getOriginalOrder(project, testFramework, true);
        }
        List<String> affectedTests = new ArrayList<>();

        String delimiter = testFramework.getDelimiter();
        for (String test: tests) {
            String clazz = test.substring(0, test.lastIndexOf(delimiter));
            if (affectedTestClasses.contains(clazz)) {
                affectedTests.add(test);
                // System.out.println("ADD TEST: " + test);
            }
        }
        return affectedTests;
    }

    public static List<String> getTestClasses (
            final MavenProject project,
            TestFramework testFramework) throws IOException {
        List<String> tests = getOriginalOrder(project, testFramework, true);

        String delimiter = testFramework.getDelimiter();
        List<String> classes = new ArrayList<>();
        for(String test : tests){
            String clazz = test.substring(0, test.lastIndexOf(delimiter));
            if(!classes.contains(clazz)) {
                classes.add(clazz);
            }
        }

        return classes;
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
                String[] elems = line.split(COMMA);
                checksumMap.put(elems[0], elems[1]);
            }
            jarCheckSums = new ArrayList<>();
            for (String path : cleanSfClassPath) {
                Pair<String, String> pair = Writer.getJarToChecksumMapping(path);
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

    private static Set<String> getImmutableList() {
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
        return immutableList;
    }

    private static boolean inImmutableList(Field field) {
        boolean isFinal = false;
        if (Modifier.isFinal(field.getModifiers())) {
            isFinal = true;
        }

        if ((field.getType().isPrimitive() || field.getDeclaringClass().isEnum()) && isFinal) {
            return true;
        }

        for (String immutableTypeName: immutableList) {
            if ((field.getType().getName().equals(immutableTypeName)) && isFinal) {
                return true;
            }
        }
        return false;
    }
}
