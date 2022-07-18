package edu.illinois.cs.dt.tools.detection.detectors;

import edu.illinois.cs.dt.tools.detection.DetectionRound;
import edu.illinois.cs.dt.tools.detection.DetectorUtil;
import edu.illinois.cs.dt.tools.detection.SmartShuffler;
import edu.illinois.cs.dt.tools.detection.TuscanShuffler;
import edu.illinois.cs.dt.tools.detection.filters.ConfirmationFilter;
import edu.illinois.cs.dt.tools.detection.filters.UniqueFilter;
import edu.illinois.cs.dt.tools.runner.InstrumentingSmartRunner;
import edu.illinois.cs.testrunner.data.results.TestRunResult;

import java.io.File;
import java.util.List;

public class TuscanDetector extends ExecutingDetector {
    private final List<String> originalOrder;
    private final TestRunResult originalResults;

    private final TuscanShuffler shuffler;

    public TuscanDetector(final InstrumentingSmartRunner runner, final File baseDir,
                                final int rounds, final List<String> tests,
                                final String type, final List<List<String>> orders) {
        super(runner, baseDir, rounds, type);

        this.originalOrder = tests;
        this.shuffler = new TuscanShuffler(tests, orders);
        this.originalResults = DetectorUtil.originalResults(originalOrder, runner);

        // Filters to be applied in order
        if (runner instanceof InstrumentingSmartRunner) {
            addFilter(new ConfirmationFilter(name, tests, (InstrumentingSmartRunner) runner));
        } else {
            addFilter(new ConfirmationFilter(name, tests, InstrumentingSmartRunner.fromRunner(runner, baseDir)));
        }

        addFilter(new UniqueFilter());
    }

    @Override
    public DetectionRound results() throws Exception {
        final List<String> order = shuffler.nextOrder();

        return makeDts(originalResults, runList(order));
    }
}
