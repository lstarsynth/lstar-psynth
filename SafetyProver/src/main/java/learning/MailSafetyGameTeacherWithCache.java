package learning;

import common.DOTPrinter;
import common.Timer;
import common.Tuple;
import common.Tuple2;
import common.VerificationUtility;
import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;
import common.finiteautomata.AutomataUtility;
import common.finiteautomata.DotGraphiczUltility;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import verification.FiniteGames;
import verification.FiniteStateSets;
import verification.InductivenessChecking;
import verification.SubsetChecking;

import java.util.*;
import java.util.function.Supplier;

public class MailSafetyGameTeacherWithCache extends SafetyGameTeacher {

    public static final Logger LOGGER = LogManager.getLogger();
    protected FiniteGames finiteStates;
    private List<CounterExample> cache = new ArrayList<>();
    private FiniteStateSets finiteStateSets;
    private boolean tryMinimalInvariant = true;

    public MailSafetyGameTeacherWithCache(int numLetters, Automata I, Automata B, Automata v_0, Automata v_1, EdgeWeightedDigraph T) {
        super(numLetters,I,B,v_0,v_1,T);
        finiteStates = new FiniteGames(v_0,v_1, I, T, B);
        Automata bad = AutomataUtility.minimiseAcyclic(AutomataUtility.getComplement(B));
        B = AutomataUtility.minimiseAcyclic(B);
        //LOGGER.debug(B.prettyPrint("safe", NoInvariantException.getIndexToLabelMapping()));
        //LOGGER.debug(bad.prettyPrint("BAD:", NoInvariantException.getIndexToLabelMapping()));
    }

    private void debug(Supplier<String> msg) {
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug(msg.get());
        }
    }

    public void setLearnMinimalInvariant(boolean trymin) {
        tryMinimalInvariant = trymin;
    }

    public boolean isAccepted(List<Integer> word)
            throws Timer.TimeoutException {
        Timer.tick();
        //LOGGER.debug("Check if word" + NoInvariantException.getLabeledWord(word) + " is reachable:");
        boolean isReachable = finiteStates.isReachable(word);
        // LOGGER.debug("Word is reachable?: " + isReachable);
        // TODO exclude or include if it is not reachable?

            boolean isBad = finiteStates.isBadReachable(word);
            //  LOGGER.debug("Is "+ NoInvariantException.getLabeledWord(word) + " bad? " + isBad);
            String labeledWord = LOGGER.isDebugEnabled() ?
                    NoInvariantException.getLabeledWord(word) : null;

            if (isBad) {
                boolean isP1reachable = finiteStates.isReachableP1(word);
                if(isP1reachable) {
                    //  LOGGER.debug("membership query P1: " + labeledWord + " is P1 reachable and bad");
                    throw new NoInvariantException(word, getInitialStates(), getTransition());
                }
                else {
                    // LOGGER.debug(labeledWord + " is reachable from P0 but not P1 and P1 can reach a bad state -> do not include in target language");
                    return false;
                }
            }
            else{
                // LOGGER.debug(" P1 cannot reach a bad state from the word " + labeledWord + " and it is reachable by either P0 or P1");
                return true;
            }

    }

    public boolean isCorrectLanguage(Automata hyp, CounterExample cex)
            throws Timer.TimeoutException {
        LOGGER.debug("found hypothesis, size " + hyp.getStates().length);
        LOGGER.debug(hyp.prettyPrint("candidate invariant:", NoInvariantException.getIndexToLabelMapping()));
        LOGGER.debug(DotGraphiczUltility.write(hyp));
        //LOGGER.debug(DOTPrinter.getString(hyp, NoInvariantException.getIndexToLabelMapping()));
        Timer.tick();
        List<Integer> ex;

        // before doing test: discharge cached counterexamples
        if(!cache.isEmpty()) {
            CounterExample cex2 = cache.remove(cache.size() - 1);
            if (cex2.isPositive() && !hyp.accepts(cex2.get())) {
                cex.addPositive(cex2.get());
                return false;
            }
            if (cex2.isNegative() && hyp.accepts(cex2.get())) {
                cex.addNegative(cex2.get());
                return false;
            }
        }

        // first test: are initial states contained?
        ex = initialCheck(hyp, getInitialStates());
        LOGGER.debug(getInitialStates().prettyPrint("\n--------------\nConstruct Initial states", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");

        Timer.tick();
        if (ex != null) {
            if (LOGGER.isDebugEnabled()) {
                String word = NoInvariantException.getLabeledWord(ex);
                LOGGER.debug("Line 89: An initial configuration is not contained in hypothesis: " + word);
            }
            boolean reachBad = finiteStates.isBadReachable(ex);

            if (reachBad) {
                String word = NoInvariantException.getLabeledWord(ex);
                if (LOGGER.isDebugEnabled()) {
                    LOGGER.debug("Line 95: Initial state is contained in bad: " + word + " ");
                }
                throw new NoInvariantException(ex, getInitialStates(), getTransition());
            }
            cex.addPositive(ex);
            LOGGER.debug(" Add positive cex: " + NoInvariantException.getLabeledWord(ex));
            return false;
        }

        // second test: are bad configurations excluded?
        Automata lang = AutomataUtility.getIntersection(hyp, getBadStates());
        ex = AutomataUtility.findSomeShortestWord(lang);
        Timer.tick();
        if (ex != null) {
            if (LOGGER.isDebugEnabled()) {
                String word = NoInvariantException.getLabeledWord(ex);
                LOGGER.debug("A bad configuration is contained in hypothesis: " + word);
            }
            cex.addNegative(ex);
            return false;
        }

        // player 0 test: is the invariant inductive?
        Tuple2<List<Integer>, List<List<Integer>>> xy = player0_closedness(hyp);
        Timer.tick();
        if (xy != null) {
            List<Integer> x = xy.x;
            String x2 = NoInvariantException.getLabeledWord(x);
            if (!finiteStates.isReachable(x)) {
/*                LOGGER.debug("* Warning: " + x2 + " is a player 0 vertex that is not reachable.");
                LOGGER.debug("* Configuration " + x2 + " should be excluded from the hypothesis.");
                addNegativeCEX(cex, x);*/
                if(!isAccepted(x)){
                    LOGGER.debug("aaa ");
                    addNegativeCEX(cex,x);
                    return false;
                }
            }
            LOGGER.debug("Hypothesis is not inductive Player 0: ");

            for (List<Integer> y : xy.y) {
                String y2 = NoInvariantException.getLabeledWord(y);
                LOGGER.debug(x2 + " => " + y2);
                boolean addPositive = !finiteStates.isBadReachable(y);
                if (addPositive) {
                    LOGGER.debug("* Configuration " + y2 + " should be included in the hypothesis.");
                    addPositiveCEX(cex, y);
                } else {
                    LOGGER.debug("* Need to look for other successors");
                }
            }
            if (!cex.exists()) {
                if (!(xy.y.size() == 0)){
                    LOGGER.debug("* Configuration " + x2 + " should be excluded from the hypothesis.");
                    LOGGER.debug(isAccepted(x));
                    addNegativeCEX(cex, x);
                    return false;
                }

            }
        }

        // player 1 test: is the invariant inductive? TODO: return more than one cex?
        xy = player1_closedness(hyp);
        Timer.tick();
        if (xy != null) {
            List<Integer> x = xy.x;
            String x2 = NoInvariantException.getLabeledWord(x);
           if (!finiteStates.isReachable(x)) {
/*                LOGGER.debug("* Warning: " + x2 + " is a player 1 vertex that is not reachable.");
                LOGGER.debug("* Configuration " + x2 + " should be excluded from the hypothesis.");
                addNegativeCEX(cex, x);*/
               if(!isAccepted(x)){

                   cex.addNegative(x);
                   return false;
               }
            }
            LOGGER.debug("Hypothesis is not inductive Player 1: ");
            for (List<Integer> y : xy.y) {
                String y2 = NoInvariantException.getLabeledWord(y);
                LOGGER.debug(x2 + " => " + y2);
                boolean addPositive = !finiteStates.isBadReachable(y);
                if (addPositive) {
                    LOGGER.debug("* Configuration " + y2 + " should be included in the hypothesis.");
                    addPositiveCEX(cex, y);
                } else {
                    LOGGER.debug("* Configuration " + x2 + " should be excluded from the hypothesis.");
                    addNegativeCEX(cex, x);
                    return false;
                }
            }
            return false;
        }

        // the candidate automaton is a proof
        return true;
    }

    private void addPositiveCEX(CounterExample cex, List<Integer> word) {
        if (!cex.exists())
            cex.addPositive(word);
        else {
            CounterExample cex2 = new CounterExample();
            cex2.addPositive(word);
            cache.add(cex2);
        }
    }

    private void addNegativeCEX(CounterExample cex, List<Integer> word) {
        if (!cex.exists())
            cex.addNegative(word);
        else {
            CounterExample cex2 = new CounterExample();
            cex2.addNegative(word);
            cache.add(cex2);
        }
    }

    /** Initial Check for safety games. Checks if the hypothesis Automaton h is contained in the
     * initial Automaton i.
     *
     * @return List<Integer> example which is a positive counterexample if the check fails or null if the check succeeds
     */
    private List<Integer> initialCheck(Automata hypothesis, Automata init){
        Automata b = AutomataUtility.getDifference(init,hypothesis);
        return b.findAcceptingString();
    }

    /**
     * Bad Check for safety games. Checks if the hypothesis Automaton h intersected with the bad state
     * Automaton bad is empty.
     *
     * @return List of Integer which is a negative counterexample if the check fails or null if the check succeeds.
     */

    private List<Integer> badCheck(Automata hypothesis, Automata badStates){
        Automata b = AutomataUtility.getIntersection(hypothesis, badStates);
        return b.findAcceptingString();

    }

    /**
     * Inductive check for Player 0 in safety games. Checks if the hypothesis Automaton h is closed
     * under Player 0 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 0 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple2<List<Integer>, List<List<Integer>>> player0_closedness(Automata hypothesis){
        // b_1 contains all vertices that have a successor in hypothesis
        Automata b_1 = AutomataUtility.toDFA(VerificationUtility.getPreImage(getTransition(), hypothesis));
        // b_2 contains all vertices of player 0 that have no successor in hypothesis
        Automata b_2 = AutomataUtility.getDifference(getPlayer0_vertices(),b_1);
        // b_3 contains contains all vertices of player 0 belonging to the hypothesis that have no successor in hypothesis
        Automata b_3 = AutomataUtility.getIntersection(b_2,hypothesis);
        List<Integer> u = b_3.findAcceptingString();
        if (u == null){
            return null;
        }
        Automata successors_of_u = VerificationUtility.getImage(u, getTransition(), getNumLetters());
        List<List<Integer>> cexs = AutomataUtility.getWords(successors_of_u, u.size());
        return new Tuple2<>(u, cexs);
    }

    /**
     * Inductive check for Player 1 in safety games. Checks if the hypothesis Automaton h is closed under
     * Player 1 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 1 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple2<List<Integer>, List<List<Integer>>> player1_closedness(Automata hypothesis){
        // b_1 contains all vertices not in b_1
        Automata b_1 = AutomataUtility.getDifference(AutomataUtility.getUnion(getPlayer0_vertices(),getPlayer1_vertices()), hypothesis);
        // b_2 contains all vertices that have a successor not belonging to hypothesis
        Automata b_2 = VerificationUtility.getPreImage(getTransition(), b_1);
        // b_3 contains all vertices of player 1 in hypothesis with at least on successor not in hypothesis
        Automata b_3 = AutomataUtility.getIntersection(AutomataUtility.getIntersection(getPlayer1_vertices(),hypothesis),b_2);
        List<Integer> u = b_3.findAcceptingString();
        if (u == null){
            return null;
        }
        // TODO maybe save successors or return multiple ones instead of redoing computation
        Automata successor_of_u = AutomataUtility.getDifference(VerificationUtility.getImage(u, getTransition(), getNumLetters()), hypothesis);
        // TODO maybe problem with termination if the same successor gets picked out again?
        List<List<Integer>> cexs = AutomataUtility.getWords(successor_of_u, u.size());
        return new Tuple2<>(u, cexs);
    }
}
