package learning;

import common.VerificationUtility;
import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class NoInvariantException extends RuntimeException {
    private static Map<Integer, String> indexToLabelMapping = null;

    public NoInvariantException() {
        super("Learner cannot find an inductive invariant with the provided teacher!");
    }

    public NoInvariantException(List<Integer> cex, Automata I, EdgeWeightedDigraph T) {
        super("Invariant does not exist! A bad configuration is reachable: " +
                getLabeledWord(cex) + "\nTrace: " + getTrace(cex, I, T));
    }

    static List<String> getTrace(List<Integer> target, Automata I, EdgeWeightedDigraph T) {
        List<List<Integer>> trace = VerificationUtility.findSomeTrace(I, target, T);
        if (trace == null) {
            return null;
        } else {
            List<String> labeledTrace = new ArrayList<>(trace.size());
            for (List<Integer> word : trace) {
                labeledTrace.add(getLabeledWord(word));
            }
            return labeledTrace;
        }
    }

    public static String getLabeledWord(List<Integer> word) {
        if (indexToLabelMapping == null)
            throw new IllegalStateException("should set IndexToLabelMapping first!");
        if (word.size() == 0) return "[]";
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        for (int index : word) {
            sb.append(indexToLabelMapping.get(index)).append(' ');
        }
        sb.setCharAt(sb.length() - 1, ']');
        return sb.toString();
    }

    public static void setIndexToLabelMapping(Map<Integer, String> indexToLabelMapping) {
        NoInvariantException.indexToLabelMapping = indexToLabelMapping;
    }

    public static Map<Integer, String> getIndexToLabelMapping() {
        return NoInvariantException.indexToLabelMapping;
    }
}

