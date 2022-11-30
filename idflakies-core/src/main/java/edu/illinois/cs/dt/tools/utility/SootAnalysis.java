package edu.illinois.cs.dt.tools.utility;

import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.spark.ondemand.pautil.SootUtil;

import soot.options.Options;
import soot.tagkit.AnnotationTag;
import soot.tagkit.VisibilityAnnotationTag;
import soot.util.queue.QueueReader;

import java.io.File;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

import static soot.SootClass.BODIES;

public class SootAnalysis {

    private static String sourceDirectory;
    private static String clzName;
    private static String methodName;
    private static List<SootMethod> entryPoints = new ArrayList();
    private static LinkedList<String> excludeList;


    private static LinkedList<String> getExcludeList() {
        if (excludeList == null) {
            excludeList = new LinkedList<String>();

            // explicitly include packages for shorter runtime:
            excludeList.add("java.*");
            excludeList.add("javax.*");
            excludeList.add("jdk.*");
            excludeList.add("soot.*");
            excludeList.add("sun.*");
            excludeList.add("sunw.*");
            excludeList.add("com.sun.*");
            excludeList.add("com.ibm.*");
            excludeList.add("com.apple.*");
            excludeList.add("android.*");
            excludeList.add("apple.awt.*");
            excludeList.add("org.apache.*");
            excludeList.add("org.xml.*");
            excludeList.add("org.codehaus.*");
        }
        return excludeList;
    }

    private static boolean inExcludeList(String className) {
        for (int i = 0; i < excludeList.size(); i++) {
            String libPackage = excludeList.get(i).substring(0, excludeList.get(i).length()-1);
            if (className.startsWith(libPackage)) {
                return true;
            }

        }
        return false;
    }

    private static void excludeJDKLibrary() {
        // exclude jdk classes
        Options.v().set_exclude(getExcludeList());
        // this option must be disabled for a sound call graph
        Options.v().set_no_bodies_for_excluded(true);
        Options.v().set_allow_phantom_refs(true);
    }

    private static void setupSoot() {
        G.reset();

        // System.out.println("EXCLUDE: " + Options.v().exclude());
        excludeJDKLibrary();
        // System.out.println("EXCLUDE: " + Options.v().exclude());

        Options.v().set_prepend_classpath(true);
        Options.v().set_app(true);
        Options.v().set_soot_classpath(sourceDirectory);
        Options.v().set_output_format(Options.output_format_jimple);
        // Options.v().set_process_dir(Collections.singletonList(sourceDirectory));
        Options.v().set_whole_program(true);
        // Options.v().set_allow_phantom_refs(true); // especially for wildfly
        entryPoints.clear();

    }

    private static void reportFieldRefInfo(Stmt stmt, final Set<String> affectedClasses) {
        FieldRef fieldRef = stmt.getFieldRef();
        // System.out.println("FIELDREF: " + fieldRef);
        fieldRef.apply(new AbstractRefSwitch() {
            @Override
            public void caseStaticFieldRef(StaticFieldRef v) {
                // A static field reference
                // System.out.println("A static field reference: " + v.getFieldRef() + " " + v.getFieldRef().isStatic());
                affectedClasses.add(v.getFieldRef().declaringClass().getName());
                // affectedClasses.add(v.getField().getName());
            }

            @Override
            public void caseInstanceFieldRef(InstanceFieldRef v) {
                // System.out.println("A instance field reference: " + v.getFieldRef() + " " + v.toString());
                // affectedClasses.add(v.getFieldRef().declaringClass().getName());
            }
        });
    }

    private static void reportFieldRefInfoForFields(Stmt stmt, final Set<String> dependentFields) {
        FieldRef fieldRef = stmt.getFieldRef();
        // System.out.println("FIELDREF: " + fieldRef);
        fieldRef.apply(new AbstractRefSwitch() {
            @Override
            public void caseStaticFieldRef(StaticFieldRef v) {
                // A static field reference
                // System.out.println("A static field reference: " + v.getFieldRef() + " " + v.getFieldRef().isStatic());
                dependentFields.add(v.getFieldRef().declaringClass().getName() + "." + v.getField().getName());
                // affectedClasses.add(v.getField().getName());
            }

            @Override
            public void caseInstanceFieldRef(InstanceFieldRef v) {
                // System.out.println("A instance field reference: " + v.getFieldRef() + " " + v.toString());
                // affectedClasses.add(v.getFieldRef().declaringClass().getName());
            }
        });
    }

    private static boolean hasBeforeOrAfterAnnotation(SootMethod sootMethod) {
        boolean hasAnnotation = false;
        VisibilityAnnotationTag tag = (VisibilityAnnotationTag) sootMethod.getTag("VisibilityAnnotationTag");
        if (tag != null) {
            for (AnnotationTag annotation : tag.getAnnotations()) {
                // System.out.println("annotation.getType(): " + annotation.getType());
                if (annotation.getType().equals("Lorg/junit/Before;") || annotation.getType().equals("Lorg/junit/After;")
                        || annotation.getType().equals("Lorg/junit/BeforeClass;") || annotation.getType().equals("Lorg/junit/AfterClass;")
                        || annotation.getType().equals("Lorg/junit/BeforeEach;") || annotation.getType().equals("Lorg/junit/AfterEach;")
                        || annotation.getType().equals("Lorg/junit/BeforeAll;") || annotation.getType().equals("Lorg/junit/AfterAll;")) {
                    // System.out.println("annotation.getType(): " + annotation.getType() + " " + sootMethod.getDeclaringClass() + "." + sootMethod.getName());
                    hasAnnotation = true;
                    break;
                }
            }
        }
        return hasAnnotation;
    }

    public static Set<String> analysis(String srcDir, String clsName, Map<String, List<String>> testClassToMethod) {
        Set<String> affectedClasses = new HashSet<>();

        sourceDirectory = srcDir;
        clzName = clsName;

        setupSoot();
        SootClass sc = Scene.v().forceResolve(clzName, BODIES);// Scene.v().loadClassAndSupport(clsName);
        sc.setApplicationClass();
        Scene.v().loadNecessaryClasses();

        try {
            // Get clinits
            for (SootMethod sm : EntryPoints.v().clinitsOf(sc)) {
                entryPoints.add(sm);
            }
        } catch (Exception e) {
            // System.out.println("CLINIT METHOD MAY NOT EXIST!");
            e.printStackTrace();
        }
        try {
            SootMethod init = sc.getMethod("<init>", new ArrayList<>());
            entryPoints.add(init);
        } catch (Exception e) {
            // System.out.println("INIT METHOD MAY NOT EXIST!");
            e.printStackTrace();
        }
        // Add the tests
        for (String test : testClassToMethod.get(clzName)) {
            try {
                String testName = test.substring(test.lastIndexOf(".") + 1);
                entryPoints.add(sc.getMethodByName(testName));
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        for (SootMethod sootMethod : sc.getMethods()) {
            try {
                if (hasBeforeOrAfterAnnotation(sootMethod)) {
                    entryPoints.add(sootMethod);
                }
            } catch (Exception e){
                // System.out.println("BUG EXISTS WHEN DETECTING @BEFORE ANNOTATIONS!");
                e.printStackTrace();
            }
        }
        Scene.v().setEntryPoints(entryPoints);
        PackManager.v().runPacks();

        int c = 1;

        // Call graph
        CallGraph callGraph = Scene.v().getCallGraph();
        ReachableMethods rm = new ReachableMethods(callGraph, entryPoints);
        rm.update();
        QueueReader qr = rm.listener();

        // System.out.println("-------------------");
        // System.out.println("-----Reachable Methods-----");

        // qr = rm.listener();
        for(Iterator<SootMethod> it = qr; it.hasNext(); ) {
            try {
                SootMethod reachableMethod = it.next();
                if (SootUtil.inLibrary(reachableMethod.getDeclaringClass().getName()) || inExcludeList(reachableMethod.getDeclaringClass().getName())) {
                    continue;
                }
                if(reachableMethod.isPhantom()) {
                    continue;
                }
                JimpleBody reachableMethodBody = (JimpleBody) reachableMethod.retrieveActiveBody();
                c = 0;
                for (Unit u : reachableMethodBody.getUnits()) {
                    c++;
                    Stmt stmt = (Stmt) u;
                    if (stmt.containsFieldRef())
                        reportFieldRefInfo(stmt, affectedClasses);
                }
            } catch (Exception e) {
                // System.out.println("LIKELY ERROR: cannot get resident body for phantom method");
                e.printStackTrace();
            }
        }

        // System.out.println("-------------------");
        // System.out.println("All the classes that could be accessed through accessing corresponding static fields. (" + clsName + ");");
        // for(String item: affectedClasses) {
        //     System.out.print(item + ";");
        // }
        // System.out.println("");

//        for (SootField sf: sc.getFields()){
//            // System.out.println(sf.getSignature());
//            if (sf.isStatic()) {
//                affectedClasses.add(clzName);
//                break;
//            }
//        }
        return affectedClasses;
    }

    public static Set<String> analysisOnFields(String srcDir, String clsName, String methodName) {
        Set<String> affectedFields = new HashSet<>();

        sourceDirectory = srcDir;
        clzName = clsName;

        setupSoot();
        SootClass sc = Scene.v().forceResolve(clzName, BODIES);// Scene.v().loadClassAndSupport(clsName);
        sc.setApplicationClass();
        Scene.v().loadNecessaryClasses();

        try {
            // Get clinits
            for (SootMethod sm : EntryPoints.v().clinitsOf(sc)) {
                entryPoints.add(sm);
            }
        } catch (Exception e) {
            // System.out.println("CLINIT METHOD MAY NOT EXIST!");
            e.printStackTrace();
        }
        try {
            SootMethod init = sc.getMethod("<init>", new ArrayList<>());
            entryPoints.add(init);
        } catch (Exception e) {
            // System.out.println("INIT METHOD MAY NOT EXIST!");
            e.printStackTrace();
        }

        String testName = methodName.substring(methodName.lastIndexOf(".") + 1);
        entryPoints.add(sc.getMethodByName(testName));

        for (SootMethod sootMethod : sc.getMethods()) {
            try {
                if (hasBeforeOrAfterAnnotation(sootMethod)) {
                    entryPoints.add(sootMethod);
                }
            } catch (Exception e){
                // System.out.println("BUG EXISTS WHEN DETECTING @BEFORE ANNOTATIONS!");
                e.printStackTrace();
            }
        }
        Scene.v().setEntryPoints(entryPoints);
        PackManager.v().runPacks();

        int c = 1;

        // Call graph
        CallGraph callGraph = Scene.v().getCallGraph();
        ReachableMethods rm = new ReachableMethods(callGraph, entryPoints);
        rm.update();
        QueueReader qr = rm.listener();

        // System.out.println("-------------------");
        // System.out.println("-----Reachable Methods-----");

        // qr = rm.listener();
        for(Iterator<SootMethod> it = qr; it.hasNext(); ) {
            try {
                SootMethod reachableMethod = it.next();
                if (SootUtil.inLibrary(reachableMethod.getDeclaringClass().getName()) || inExcludeList(reachableMethod.getDeclaringClass().getName())) {
                    continue;
                }
                if(reachableMethod.isPhantom()) {
                    continue;
                }
                JimpleBody reachableMethodBody = (JimpleBody) reachableMethod.retrieveActiveBody();
                c = 0;
                for (Unit u : reachableMethodBody.getUnits()) {
                    c++;
                    Stmt stmt = (Stmt) u;
                    if (stmt.containsFieldRef())
                        reportFieldRefInfoForFields(stmt, affectedFields);
                }
            } catch (Exception e) {
                // System.out.println("LIKELY ERROR: cannot get resident body for phantom method");
                e.printStackTrace();
            }
        }

        return affectedFields;
    }
}

