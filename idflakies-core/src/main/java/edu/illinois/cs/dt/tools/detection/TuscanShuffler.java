package edu.illinois.cs.dt.tools.detection;

import java.util.*;

public class TuscanShuffler {
    private final List<String> tests;
    private final List<List<String>> tuscanOrders;
    private int index;

    public TuscanShuffler(final List<String> tests, List<List<String>> orders) {
        this.tests = new ArrayList<>(tests);
        this.tuscanOrders = orders;
        this.index = 0;

    }

    public List<String> nextOrder() {
        if (index == tuscanOrders.size()) {
            return new LinkedList<>();
        }
        List<String> order = tuscanOrders.get(index);
        // System.out.println("INDEX: " + index + "; ORDER: " + order.toString());
        index ++;
        return order;
    }
}
