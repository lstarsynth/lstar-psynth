package common.finiteautomata;

import common.IntPair;
import common.VerificationUtility;
import common.bellmanford.DirectedEdgeWithInputOutput;
import de.libalf.BasicAutomaton;
import de.libalf.BasicTransition;

import java.util.*;


public class AutomataUtility {
    public static Automata toDFA(Automata automata) {
        List<State> allStatesDFA = new ArrayList<State>();
        Map<Set<Integer>, State> mapStates = new HashMap<Set<Integer>, State>();

        Stack<Set<Integer>> workingStates = new Stack<Set<Integer>>();
        Set<Integer> initSet = automata.getEpsilonClosure(automata.getInitStateId());
        final boolean hasEpsilon = automata.hasEpsilonTransitions();

        workingStates.push(initSet);

        //state 0 will be the init state in new DFA
        State initInDFA = new State(0);
        mapStates.put(initSet, initInDFA);
        allStatesDFA.add(initInDFA);

        while (!workingStates.isEmpty()) {
            Set<Integer> statesInNFA = workingStates.pop();
            State stateInDFA = mapStates.get(statesInNFA);

            for (int i = 0; i < automata.getNumLabels(); i++) {
                Set<Integer> destsInNFA =
                        automata.getDests(statesInNFA, i);
                if (hasEpsilon)
                    destsInNFA =
                            automata.getEpsilonClosure(destsInNFA);

                if (!destsInNFA.isEmpty()) {
                    State destInDFA = mapStates.get(destsInNFA);

                    if (destInDFA == null) {
                        destInDFA = new State(mapStates.size());
                        mapStates.put(destsInNFA, destInDFA);
                        allStatesDFA.add(destInDFA);

                        //new
                        workingStates.push(destsInNFA);
                    }

                    stateInDFA.addTrans(i, destInDFA.getId());
                }
            }
        }

        Automata dfa = new Automata(initInDFA.getId(), allStatesDFA, automata.getNumLabels());

        //compute accepting states
        Set<Integer> acceptingDFA = new HashSet<Integer>();
        for (Set<Integer> statesNFA : mapStates.keySet()) {
            for (Integer stateNFA : statesNFA) {
                if (automata.getAcceptingStateIds().contains(stateNFA)) {
                    acceptingDFA.add(mapStates.get(statesNFA).getId());
                    break;
                }
            }
        }
        dfa.setAcceptingStateIds(acceptingDFA);

        //
        return dfa;
    }

    public static Automata toCompleteDFA(Automata dfa) {
        int init = dfa.getInitStateId();
        int numberOfLabels = dfa.getNumLabels();
        List<State> states = new ArrayList<State>(Arrays.asList(dfa.getStates()));
        Set<Integer> accepting = dfa.getAcceptingStateIds();

        Automata result = new Automata(init, states.size() + 1, numberOfLabels);
        result.setAcceptingStateIds(new HashSet<Integer>(accepting));

        int dummyState = states.size();

        //copy transition
        for (State state : states) {
            for (int i = 0; i < numberOfLabels; i++) {
                Set<Integer> nexts = state.getDestIds(i);
                if (nexts.isEmpty()) {
                    //add transition to dummy
                    result.addTrans(state.getId(), i, dummyState);
                } else {
                    for (int next : nexts) {
                        result.addTrans(state.getId(), i, next);
                    }
                }
            }
        }

        //loop at dummy
        for (int i = 0; i < numberOfLabels; i++) {
            result.addTrans(dummyState, i, dummyState);
        }

        return result;
    }

    public static Automata pruneUnreachableStates(Automata dfa) {
        List<State> states = new ArrayList<State>(Arrays.asList(dfa.getStates()));
        final int numStates = states.size();
        final int numLabels = dfa.getNumLabels();

        boolean reachable[] = new boolean[numStates];

        // forward

        reachable[dfa.getInitStateId()] = true;

        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < numStates; ++i)
                if (reachable[i])
                    for (int l = 0; l < numLabels; ++l)
                        for (int j : states.get(i).getDestIds(l))
                            if (!reachable[j]) {
                                changed = true;
                                reachable[j] = true;
                            }
        }

        // backward

        boolean backwardReachable[] = new boolean[numStates];

        for (int a : dfa.getAcceptingStateIds())
            if (reachable[a])
                backwardReachable[a] = true;

        changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < numStates; ++i)
                if (reachable[i] && !backwardReachable[i])
                    reachLoop:for (int l = 0; l < numLabels; ++l)
                        for (int j : states.get(i).getDestIds(l))
                            if (backwardReachable[j]) {
                                changed = true;
                                backwardReachable[i] = true;
                                break reachLoop;
                            }
        }

        int mapping[] = new int[numStates];
        int num = 0;
        for (int i = 0; i < numStates; ++i)
            if (backwardReachable[i]) {
                mapping[i] = num;
                ++num;
            } else {
                mapping[i] = -1;
            }

        if (num == 0)
            return new Automata(0, 1, numLabels);

        Automata result = new Automata(mapping[dfa.getInitStateId()],
                num, numLabels);

        Set<Integer> newAccepting = new HashSet<Integer>();
        for (int a : dfa.getAcceptingStateIds())
            if (mapping[a] >= 0)
                newAccepting.add(mapping[a]);
        result.setAcceptingStateIds(newAccepting);

        for (int i = 0; i < numStates; ++i)
            if (backwardReachable[i]) {
                State state = states.get(i);
                for (int l = 0; l < numLabels; ++l)
                    for (int dest : state.getDestIds(l))
                        if (backwardReachable[dest])
                            result.addTrans(mapping[i], l, mapping[dest]);
            }

        return result;
    }

    /**
     * Turn a complete DFA into a minimal DFA.
     */
    public static Automata toMinimalDFA(Automata dfa) {
        final State[] states = dfa.getStates();
        final int numStates = states.length;
        final long numStatesLong = (long) numStates;
        final int numLabels = dfa.getNumLabels();
        final Set<Integer> accepting = dfa.getAcceptingStateIds();

        final Set<Integer>[][] invTransitionsSet =
                new Set[numStates][numLabels];

        for (int s = 0; s < numStates; ++s)
            for (int l = 0; l < numLabels; ++l)
                invTransitionsSet[s][l] = new HashSet<Integer>();

        for (int s = 0; s < numStates; ++s) {
            final State state = states[s];
            for (int l = 0; l < numLabels; ++l)
                for (int dest : state.getDestIds(l))
                    invTransitionsSet[dest][l].add(s);
        }

        final int[][][] invTransitions =
                new int[numStates][numLabels][];

        for (int s = 0; s < numStates; ++s)
            for (int l = 0; l < numLabels; ++l) {
                Set<Integer> set = invTransitionsSet[s][l];
                int[] ar = new int[set.size()];
                int i = 0;
                for (int x : set)
                    ar[i++] = x;
                invTransitions[s][l] = ar;
            }

        final BitSet[] nonEqStates = new BitSet[numStates];
        final Stack<Long> todo = new Stack<Long>();

        // initialise
        for (int i = 0; i < numStates; ++i)
            for (int j = 0; j < i; ++j)
                if (accepting.contains(i) != accepting.contains(j)) {
                    if (nonEqStates[i] == null)
                        nonEqStates[i] = new BitSet();
                    nonEqStates[i].set(j);
                    todo.push(i * numStatesLong + j);
                }

        // fixed-point iteration
        while (!todo.empty()) {
            final long nextPair = todo.pop();
            final int state1Id = (int) (nextPair / numStatesLong);
            final int state2Id = (int) (nextPair % numStatesLong);

            for (int l = 0; l < numLabels; ++l) {
                final int[] pre1 = invTransitions[state1Id][l];
                if (pre1.length == 0)
                    continue;

                final int[] pre2 = invTransitions[state2Id][l];
                if (pre2.length == 0)
                    continue;

                for (int s1 : pre1)
                    for (int s2 : pre2)
                        if (s1 != s2) {
                            final int smaller, bigger;
                            if (s1 > s2) {
                                bigger = s1;
                                smaller = s2;
                            } else {
                                bigger = s2;
                                smaller = s1;
                            }

                            if (nonEqStates[bigger] == null)
                                nonEqStates[bigger] = new BitSet();

                            if (!nonEqStates[bigger].get(smaller)) {
                                nonEqStates[bigger].set(smaller);
                                final long ind =
                                        bigger * numStatesLong + smaller;
                                todo.push(ind);
                            }
                        }
            }
        }

        int[] mapping = new int[numStates];
        Arrays.fill(mapping, -1);
        int num = 0;
        for (int i = 0; i < numStates; ++i)
            if (mapping[i] < 0) {
                mapping[i] = num;
                for (int j = i + 1; j < numStates; ++j)
                    if (nonEqStates[j] == null || !nonEqStates[j].get(i))
                        mapping[j] = num;
                ++num;
            }

        Automata result = mapStates(dfa, mapping, num, true);

        //            System.out.println("" + numStates + " -> " + result.getStates().length);
        return result;
    }

    public static Automata mergeStates(Automata dfa) {
        final State[] states = dfa.getStates();
        final int numStates = states.length;
        final int numLabels = dfa.getNumLabels();
        final Set<Integer> accepting = dfa.getAcceptingStateIds();

        final Map<List<Integer>, Integer> seenStates =
                new HashMap<List<Integer>, Integer>();

        int[] oldMapping = new int[numStates];
        int[] mapping = new int[numStates];

        for (int i = 0; i < numStates; ++i)
            oldMapping[i] = i;

        boolean changed = true;
        while (changed) {
            changed = false;
            seenStates.clear();

            for (int s = 0; s < numStates; ++s) {
                final State state = states[s];

                final List<Integer> sig = new ArrayList<Integer>();
                sig.add(accepting.contains(s) ? 1 : 0);

                for (int l = 0; l < numLabels; ++l) {
                    final Set<Integer> dest = state.getDestIds(l);
                    if (dest.isEmpty()) {
                        sig.add(-1);
                    } else {
                        assert (dest.size() == 1);
                        sig.add(oldMapping[dest.iterator().next()]);
                    }
                }

                final Integer oldS = seenStates.get(sig);
                if (oldS == null) {
                    final int next = seenStates.size();
                    seenStates.put(sig, next);
                    mapping[s] = next;
                } else {
                    mapping[s] = oldS;
                }

                if (mapping[s] != oldMapping[s])
                    changed = true;
            }

            int[] t = oldMapping;
            oldMapping = mapping;
            mapping = t;
        }

        if (seenStates.size() == states.length)
            return dfa;

        return mapStates(dfa, mapping, seenStates.size(), false);
    }

    private static Automata mapStates(Automata dfa,
                                      int[] mapping,
                                      int newStateNum,
                                      boolean hideDeadEnd) {
        final State[] states = dfa.getStates();
        final int numLabels = dfa.getNumLabels();
        final Set<Integer> accepting = dfa.getAcceptingStateIds();

        Automata result = new Automata(mapping[dfa.getInitStateId()],
                newStateNum, numLabels);

        Set<Integer> newAccepting = new HashSet<Integer>();
        for (int a : accepting)
            newAccepting.add(mapping[a]);
        result.setAcceptingStateIds(newAccepting);

        int deadEnd;
        if (hideDeadEnd) {
            outer:
            for (deadEnd = 0; deadEnd < newStateNum; ++deadEnd) {
                if (newAccepting.contains(deadEnd))
                    continue;

                for (State state : states)
                    if (mapping[state.getId()] == deadEnd)
                        for (int l = 0; l < numLabels; ++l)
                            for (int dest : state.getDestIds(l))
                                if (mapping[dest] != deadEnd)
                                    continue outer;

                break;
            }
        } else {
            deadEnd = newStateNum;
        }

        for (State state : states)
            for (int l = 0; l < numLabels; ++l)
                for (int dest : state.getDestIds(l))
                    if (mapping[dest] != deadEnd)
                        result.addTrans(mapping[state.getId()],
                                l,
                                mapping[dest]);

        return result;
    }

    public static Automata getComplement(Automata automata) {
        if (!automata.isDFA()) {
            automata = toDFA(automata);
        }

        if (!automata.isCompleteDFA()) {
            automata = toCompleteDFA(automata);
        }
        Automata result = new Automata(automata.getInitStateId(), Arrays.asList(automata.getStates()), automata.getNumLabels());

        Set<Integer> acceptings = automata.getAcceptingStateIds();
        Set<Integer> complementAccepting = new HashSet<Integer>();
        for (int state = 0; state < automata.getStates().length; state++) {
            if (!acceptings.contains(state)) {
                complementAccepting.add(state);
            }
        }

        result.setAcceptingStateIds(complementAccepting);

        return result;
    }

    /**
     * Turn an arbitrary automaton into a minimal DFA.
     */
    public static Automata minimise(Automata automata) {
        if (!automata.isDFA()) {
            automata = toDFA(automata);
        }

        if (!automata.isCompleteDFA()) {
            automata = toCompleteDFA(automata);
        }

        return toMinimalDFA(automata);
    }

    /**
     * Turn an acyclic automaton into a minimal DFA.
     */
    public static Automata minimiseAcyclic(Automata automata) {
        if (!automata.isDFA()) {
            automata = toDFA(automata);
        }

        return mergeStates(pruneUnreachableStates(automata));
    }

    /**
     * Compute all words of length <code>wordLength</code> accepted by the
     * given automaton.
     */
    public static List<List<Integer>> getWords(Automata lang, int wordLength) {
        return getWords(lang, wordLength, Integer.MAX_VALUE);
    }

    /**
     * Compute at most <code>maxWords</code> words of length
     * <code>wordLength</code> accepted by the
     * given automaton.
     */
    public static List<List<Integer>> getWords(Automata lang,
                                               int wordLength,
                                               int maxWords) {
        List<List<Integer>> res = new ArrayList<List<Integer>>();
        try {
            exploreWords(lang.getInitState(),
                    lang, wordLength,
                    new ArrayList<Integer>(),
                    res,
                    maxWords);
        } catch (TooManyWordsException e) {
        }
        return res;
    }

    public static Automata getUnion(Automata B, Automata F) {
        int numStatesB = B.getStates().length;
        int numStatesF = F.getStates().length;

        int numStatesBF = 1 + numStatesB + numStatesF;
        Automata result = new Automata(0, numStatesBF, B.getNumLabels());

        int offsetStateB = 1;
        int offsetStateF = offsetStateB + numStatesB;

        Set<Integer> acceptings = new HashSet<Integer>();
        for (int acceptB : B.getAcceptingStateIds()) {
            acceptings.add(acceptB + offsetStateB);
        }

        for (int acceptF : F.getAcceptingStateIds()) {
            acceptings.add(acceptF + offsetStateF);
        }

        if (B.getAcceptingStateIds().contains(B.getInitStateId()) ||
                F.getAcceptingStateIds().contains(F.getInitStateId()))
            acceptings.add(0);

        result.setAcceptingStateIds(acceptings);

        //add empty transition from new init to 2 inits of B, F
        //		result.addTrans(0, Automata.EPSILON_LABEL, B.getSourceVertex() + offsetStateB);
        //		result.addTrans(0, Automata.EPSILON_LABEL, F.getSourceVertex() + offsetStateF);

        List<DirectedEdgeWithInputOutput> edgesB = getEdges(B);
        for (DirectedEdgeWithInputOutput edgeB : edgesB) {
            result.addTrans(edgeB.from() + offsetStateB, edgeB.getInput(), edgeB.to() + offsetStateB);
            if (edgeB.from() == B.getInitStateId())
                result.addTrans(0, edgeB.getInput(), edgeB.to() + offsetStateB);
        }

        List<DirectedEdgeWithInputOutput> edgesF = getEdges(F);
        for (DirectedEdgeWithInputOutput edgeF : edgesF) {
            result.addTrans(edgeF.from() + offsetStateF, edgeF.getInput(), edgeF.to() + offsetStateF);
            if (edgeF.from() == F.getInitStateId())
                result.addTrans(0, edgeF.getInput(), edgeF.to() + offsetStateF);
        }

        return result;

    }

    public static Automata getUniversalAutomaton(int numLetters) {
        Automata result = new Automata(0, 1, numLetters);

        Set<Integer> acceptings = new HashSet<Integer>();
        acceptings.add(0);
        result.setAcceptingStateIds(acceptings);

        for (int i = 0; i < numLetters; ++i)
            result.addTrans(0, i, 0);

        return result;
    }

    public static Automata getIntersection(Automata B, Automata F) {
        int numStatesB = B.getStates().length;
        int numStatesF = F.getStates().length;

        int numStatesBF = numStatesB * numStatesF;
        Automata result = new Automata(VerificationUtility.hash(B.getInitStateId(), F.getInitStateId(), numStatesB),
                numStatesBF, B.getNumLabels());

        Set<Integer> acceptings = new HashSet<Integer>();
        for (int acceptB : B.getAcceptingStateIds())
            for (int acceptF : F.getAcceptingStateIds())
                acceptings.add(VerificationUtility.hash(acceptB, acceptF, numStatesB));

        result.setAcceptingStateIds(acceptings);

        List<DirectedEdgeWithInputOutput> edgesB = getEdges(B);
        List<DirectedEdgeWithInputOutput> edgesF = getEdges(F);

        for (DirectedEdgeWithInputOutput edgeB : edgesB)
            for (DirectedEdgeWithInputOutput edgeF : edgesF)
                if (edgeB.getInput() == edgeF.getInput())
                    result.addTrans(VerificationUtility.hash(edgeB.from(), edgeF.from(), numStatesB),
                            edgeB.getInput(),
                            VerificationUtility.hash(edgeB.to(), edgeF.to(), numStatesB));

        return pruneUnreachableStates(result);
    }

    public static Automata getDifference(Automata A, Automata B) {
        return getIntersectionLazily(A, B, true);
    }

    public static Automata getIntersectionLazily(Automata A, Automata B) {
        return getIntersectionLazily(A, B, false);
    }

    private static Automata getIntersectionLazily(Automata A, Automata B, boolean complementB) {
        //	    System.out.println("A: " + A);
        //	    System.out.println("B: " + B);
        final int numLetters = A.getNumLabels();
        final State[] statesA = A.getStates();
        final State[] statesB = B.getStates();
        final int numStatesB = statesB.length;
        final Set<Integer> acceptingA = A.getAcceptingStateIds();
        final Set<Integer> acceptingB = B.getAcceptingStateIds();

        if (complementB && !B.isDFA()) throw new IllegalStateException("The second automaton mush be a DFA.");

        final List<IntPair> newStates = new ArrayList<IntPair>();
        final Map<IntPair, Integer> stateId = new HashMap<IntPair, Integer>();

        newStates.add(new IntPair(A.getInitStateId(), B.getInitStateId()));
        stateId.put(newStates.get(0), 0);

        final List<Integer> transFrom = new ArrayList<Integer>();
        final List<Integer> transLabel = new ArrayList<Integer>();
        final List<Integer> transTo = new ArrayList<Integer>();

        final Set<Integer> dummyBStates = new HashSet<Integer>();
        dummyBStates.add(numStatesB);

        for (int nextToProcess = 0;
             nextToProcess < newStates.size();
             ++nextToProcess) {
            final IntPair state = newStates.get(nextToProcess);
            final State stateA = statesA[state.a];

            for (int l : stateA.getOutgoingLabels()) {
                Set<Integer> destsB;
                if (complementB) {
                    if (state.b == numStatesB) {
                        destsB = dummyBStates;
                    } else {
                        destsB = statesB[state.b].getDestIds(l);
                        if (destsB.isEmpty())
                            destsB = dummyBStates;
                    }
                } else {
                    destsB = statesB[state.b].getDestIds(l);
                }

                for (int destA : stateA.getDestIds(l))
                    for (int destB : destsB) {
                        final IntPair dest = new IntPair(destA, destB);

                        Integer destId = stateId.get(dest);
                        if (destId == null) {
                            destId = newStates.size();
                            stateId.put(dest, destId);
                            newStates.add(dest);
                        }

                        transFrom.add(nextToProcess);
                        transLabel.add(l);
                        transTo.add(destId);
                    }
            }
        }

        final Automata result = new Automata(0, newStates.size(), numLetters);

        for (int i = 0; i < transFrom.size(); ++i)
            result.addTrans(transFrom.get(i), transLabel.get(i), transTo.get(i));

        Set<Integer> acceptings = new HashSet<Integer>();
        for (int i = 0; i < newStates.size(); ++i) {
            final IntPair state = newStates.get(i);
            if (acceptingA.contains(state.a) &&
                    (complementB != acceptingB.contains(state.b)))
                acceptings.add(i);
        }

        result.setAcceptingStateIds(acceptings);

        return result;
    }

    public static List<DirectedEdgeWithInputOutput> getEdges(Automata automata) {
        List<DirectedEdgeWithInputOutput> result = new ArrayList<DirectedEdgeWithInputOutput>();

        int dummyOutput = -1;
        for (State state : automata.getStates()) {
            for (int label = 0; label < automata.getNumLabels(); label++) {
                Set<Integer> dests = state.getDestIds(label);
                for (int dest : dests) {
                    DirectedEdgeWithInputOutput edge = new DirectedEdgeWithInputOutput(state.getId(), dest, label, dummyOutput);
                    result.add(edge);
                }
            }
        }

        return result;
    }

    private static class TooManyWordsException extends RuntimeException {
    }

    private static void exploreWords(State state,
                                     Automata lang,
                                     int wordLength,
                                     List<Integer> currentWord,
                                     List<List<Integer>> result,
                                     int maxWords) {
        if (wordLength == 0) {
            if (lang.getAcceptingStateIds().contains(state.getId())) {
                List<Integer> finalWord = new ArrayList<Integer>();
                finalWord.addAll(currentWord);
                result.add(finalWord);
                if (result.size() >= maxWords)
                    throw new TooManyWordsException(); // break the recursion
            }
        } else {
            for (int l : state.getOutgoingLabels()) {
                currentWord.add(l);
                for (int id : state.getDestIds(l))
                    exploreWords(lang.getStates()[id],
                            lang,
                            wordLength - 1,
                            currentWord,
                            result,
                            maxWords);
                currentWord.remove(currentWord.size() - 1);
            }
        }
    }

    /**
     * Compute a word accepted by the given automaton; or
     * <code>null</code> if the accepted language is empty
     */
    public static List<Integer> findSomeWord(Automata lang) {
        final List<Integer> res = new ArrayList<Integer>();
        if (findSomeWordHelpter(lang.getStates()[lang.getInitStateId()],
                lang,
                res,
                new boolean[lang.getStates().length]))
            return res;
        return null;
    }

    private static boolean findSomeWordHelpter(State state,
                                               Automata lang,
                                               List<Integer> currentWord,
                                               boolean[] seenStates) {
        if (lang.getAcceptingStateIds().contains(state.getId()))
            return true;
        for (int l : state.getOutgoingLabels()) {
            currentWord.add(l);
            for (int id : state.getDestIds(l)) {
                if (!seenStates[id]) {
                    seenStates[id] = true;
                    if (findSomeWordHelpter(lang.getStates()[id],
                            lang,
                            currentWord,
                            seenStates))
                        return true;
                }
            }
            currentWord.remove(currentWord.size() - 1);
        }

        return false;
    }

    /**
     * Compute a word accepted by the given automaton; or
     * <code>null</code> if the accepted language is empty
     */
    public static List<Integer> findSomeShortestWord(Automata lang) {
        final State[] states = lang.getStates();
        final int N = states.length;
        final List<Integer>[] words = new List[N];

        for (int i : lang.getAcceptingStateIds())
            words[i] = new ArrayList<Integer>();

        boolean changed = true;
        while (changed) {
            changed = false;

            for (int i = 0; i < N; ++i) {
                final State state = states[i];
                List<Integer> shortestSucc = null;
                int shortestSuccLabel = -1;

                for (int l : state.getOutgoingLabels())
                    for (int id : state.getDestIds(l))
                        if (shortestSucc == null ||
                                (words[id] != null &&
                                        words[id].size() < shortestSucc.size())) {
                            shortestSucc = words[id];
                            shortestSuccLabel = l;
                        }

                if (shortestSucc != null &&
                        (words[i] == null ||
                                words[i].size() > shortestSucc.size() + 1)) {
                    changed = true;
                    words[i] = new ArrayList<Integer>();
                    words[i].add(shortestSuccLabel);
                    words[i].addAll(shortestSucc);
                }
            }
        }

        return words[lang.getInitStateId()];
    }

    public static Automata getWordAutomaton(Automata aut, int wordLength) {
        Automata lengthAut = new Automata(0, wordLength + 1, aut.getNumLabels());

        Set<Integer> acceptings = new HashSet<Integer>();
        acceptings.add(wordLength);
        lengthAut.setAcceptingStateIds(acceptings);

        for (int l = 0; l < aut.getNumLabels(); ++l)
            for (int s = 0; s < wordLength; ++s)
                lengthAut.addTrans(s, l, s + 1);
        return minimise(getIntersection(lengthAut, aut));
    }

    public static Automata closeUnderRotation(Automata aut) {
        final State[] autStates = aut.getStates();
        final int N = autStates.length;
        final int numLetters = aut.getNumLabels();
        final Automata result =
                new Automata(0, N * N * 2 + 1, aut.getNumLabels());

        // copy the automata transitions
        for (int s = 0; s < N; ++s)
            for (int l = 0; l < numLetters; ++l)
                for (int t : autStates[s].getDestIds(l))
                    for (int i = 0; i < N * 2; ++i)
                        result.addTrans(1 + i * N + s, l, 1 + i * N + t);

        // accepting states
        Set<Integer> acceptings = new HashSet<Integer>();

        for (int i = 0; i < N; ++i)
            acceptings.add(1 + i * 2 * N + N + i);

        result.setAcceptingStateIds(acceptings);

        // add epsilon transitions
        for (int s : aut.getAcceptingStateIds())
            for (int i = 0; i < N; ++i)
                result.addTrans(1 + i * 2 * N + s,
                        Automata.EPSILON_LABEL,
                        1 + i * 2 * N + N + aut.getInitStateId());

        for (int i = 0; i < N; ++i)
            result.addTrans(0, Automata.EPSILON_LABEL, 1 + i * 2 * N + i);

        return minimise(result);
    }

    public static Automata closeUnderRotation(Automata aut,
                                              List<Integer> startLetters) {
        final Automata closure = closeUnderRotation(aut);

        final Automata prefixAut = new Automata(0, 2, aut.getNumLabels());

        for (int l : startLetters)
            prefixAut.addTrans(0, l, 1);
        for (int l = 0; l < aut.getNumLabels(); ++l)
            prefixAut.addTrans(1, l, 1);

        final Set<Integer> acceptings = new HashSet<Integer>();
        acceptings.add(1);
        prefixAut.setAcceptingStateIds(acceptings);

        final Automata restrictedClosure =
                getIntersectionLazily(closure, prefixAut);
        final Automata result =
                minimise(getUnion(restrictedClosure, aut));
        return result;
    }

    public static BasicAutomaton SLRP2Alf(Automata from) {
        BasicAutomaton to = new BasicAutomaton(from.isDFA(), from.getNumStates(), from.getNumLabels());
        to.addInitialState(from.getInitStateId());
        for (int state : from.getAcceptingStateIds()) {
            to.addFinalState(state);
        }
        for (State source : from.getStates()) {
            for (Integer label : source.getOutgoingLabels()) {
                for (Integer dest : source.getDestIds(label)) {
                    to.addTransition(new BasicTransition(source.getId(), label, dest));
                }
            }
        }
        return to;
    }

    public static Automata Alf2SLRP(BasicAutomaton from) {
        Set<Integer> init = from.getInitialStates();
        Automata to;
        if (init.size() > 1) {
            int initState = from.getNumberOfStates();
            to = new Automata(
                    initState,
                    from.getNumberOfStates() + 1,
                    from.getAlphabetSize());
            for (BasicTransition t : from.getTransitions()) {
                to.addTrans(t.source, t.label, t.destination);
            }
            to.setAcceptingStateIds(from.getFinalStates());
            Iterator<Integer> it = init.iterator();
            while (it.hasNext()) to.addTrans(initState, Automata.EPSILON_LABEL, it.next());
        } else {
            int initState = init.iterator().next();
            to = new Automata(
                    initState,
                    from.getNumberOfStates(),
                    from.getAlphabetSize());
            for (BasicTransition t : from.getTransitions()) {
                to.addTrans(t.source, t.label, t.destination);
            }
            to.setAcceptingStateIds(from.getFinalStates());
        }
        return to;
    }
}
