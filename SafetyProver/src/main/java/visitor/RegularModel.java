package visitor;

import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;

import java.util.*;

public class RegularModel {
    private Automata I;
    private Automata B;
    private EdgeWeightedDigraph T;
    private Automata P0;
    private Automata P1;

    private Map<String, Integer> labelToIndex = new HashMap<String, Integer>();
    private int numberOfLetters;

    private int minNumOfStatesTransducer = 0;
    private int maxNumOfStatesTransducer = 0;

    private int minNumOfStatesAutomaton = 0;
    private int maxNumOfStatesAutomaton = 0;

    private int minNumOfInitStatesAutomaton = 0;
    private int maxNumOfInitStatesAutomaton = 0;

    private int logLevel = 0;
    private int parLevel = 0;

    private boolean closeInitStates = false;
    private boolean useRankingFunctions = false;
    private boolean alwaysMonolithic = false;
    private boolean precomputedInv = true;

    private List<String> symmetries = new ArrayList<String>();

    private int explicitChecksUntilLength = -1;
    private Map<Integer, String> indexToLabel;

    public Automata getI() {
        return I;
    }

    public void setI(Automata initial) {
        I = initial;
    }

    public EdgeWeightedDigraph getT() {
        return T;
    }

    public Automata getB() {
        return B;
    }

    public void setB(Automata bad) {
        B = bad;
    }

    public EdgeWeightedDigraph getPlayer1() {
        return null;
    }

    public void setT(EdgeWeightedDigraph transition) {
        this.T = transition;
    }

    public Automata getP0() {
        return P0;
    }

    public void setP0(Automata p0) {
        P0 = p0;
    }

    public Automata getP1() {
        return P1;
    }

    public void setP1(Automata p1) {
        P1 = p1;
    }

    public void setLabelToIndex(Map<String, Integer> labelToIndex) {
        this.labelToIndex = Collections.unmodifiableMap(labelToIndex);
    }

    public Map<Integer, String> getIndexToLabel() {
        if (indexToLabel == null) {
            Map<Integer, String> map = new HashMap<Integer, String>();
            for (Map.Entry<String, Integer> entry : labelToIndex.entrySet())
                map.put(entry.getValue(), entry.getKey());
            indexToLabel = Collections.unmodifiableMap(map);
        }
        return indexToLabel;
    }

    public int getNumberOfLetters() {
        return numberOfLetters;
    }

    public void setNumberOfLetters(int numberOfLetters) {
        this.numberOfLetters = numberOfLetters;
    }

    public int getMinNumOfStatesTransducer() {
        return minNumOfStatesTransducer;
    }

    public void setMinNumOfStatesTransducer(int minNumOfStatesTransducer) {
        this.minNumOfStatesTransducer = minNumOfStatesTransducer;
    }

    public int getMaxNumOfStatesTransducer() {
        return maxNumOfStatesTransducer;
    }

    public void setMaxNumOfStatesTransducer(int maxNumOfStatesTransducer) {
        this.maxNumOfStatesTransducer = maxNumOfStatesTransducer;
    }

    public int getMinNumOfStatesAutomaton() {
        return minNumOfStatesAutomaton;
    }

    public void setMinNumOfStatesAutomaton(int minNumOfStatesAutomaton) {
        this.minNumOfStatesAutomaton = minNumOfStatesAutomaton;
    }

    public int getMaxNumOfStatesAutomaton() {
        return maxNumOfStatesAutomaton;
    }

    public void setMaxNumOfStatesAutomaton(int maxNumOfStatesAutomaton) {
        this.maxNumOfStatesAutomaton = maxNumOfStatesAutomaton;
    }

    public int getMinNumOfInitStatesAutomaton() {
        return minNumOfInitStatesAutomaton;
    }

    public void setMinNumOfInitStatesAutomaton(int minNumOfStatesAutomaton) {
        this.minNumOfInitStatesAutomaton = minNumOfStatesAutomaton;
    }

    public int getMaxNumOfInitStatesAutomaton() {
        return maxNumOfInitStatesAutomaton;
    }

    public void setMaxNumOfInitStatesAutomaton(int maxNumOfStatesAutomaton) {
        this.maxNumOfInitStatesAutomaton = maxNumOfStatesAutomaton;
    }

    public boolean getCloseInitStates() {
        return closeInitStates;
    }

    public void setCloseInitStates(boolean t) {
        closeInitStates = t;
    }

    public void addSymmetry(String symm) {
        symmetries.add(symm);
    }

    public List<String> getSymmetries() {
        return symmetries;
    }

    public void setExplicitChecksUntilLength(int len) {
        explicitChecksUntilLength = len;
    }

    public int getExplicitChecksUntilLength() {
        return explicitChecksUntilLength;
    }

    public boolean getUseRankingFunctions() {
        return useRankingFunctions;
    }

    public void setUseRankingFunctions(boolean t) {
        useRankingFunctions = t;
    }

    public boolean getAlwaysMonolithic() {
        return alwaysMonolithic;
    }

    public void setAlwaysMonolithic(boolean t) {
        alwaysMonolithic = t;
    }

    public boolean getPrecomputedInv() {
        return precomputedInv;
    }

    public void setPrecomputedInv(boolean t) {
        precomputedInv = t;
    }

    public int getLogLevel() {
        return logLevel;
    }

    public void setLogLevel(int t) {
        logLevel = t;
    }

    public int getParLevel() {
        return parLevel;
    }

    public void setParLevel(int t) {
        parLevel = t;
    }
}

// vim: tabstop=4
