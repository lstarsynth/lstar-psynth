package verification;

import common.Timer;
import common.VerificationUtility;
import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;
import common.finiteautomata.AutomataUtility;
import learning.NoInvariantException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;

public class FiniteGames {
    private static final Logger LOGGER = LogManager.getLogger();
    private final Automata v_0,v_1, B, I;
    private final EdgeWeightedDigraph T;
    private final Map<Integer, Set<List<Integer>>> reachableStates =
            new HashMap<Integer, Set<List<Integer>>>();
    private final Map<Integer, Automata> reachableStateAutomata =
            new HashMap<Integer, Automata>();
    private FiniteStateSets finiteStateSets;
    private int k = 0;

    public FiniteGames(Automata v_0, Automata v_1, Automata I, EdgeWeightedDigraph T, Automata B) {
        this.v_0 = v_0;
        this.v_1 = v_1;
        this.T = T;
        this.B = B;
        this.I = I;
        finiteStateSets = new FiniteStateSets(I,T,B);

    }
    // TODO does not work properly, computes only 1 step and terminates? check amount of steps. check the computed predecessors of Bad
    public Automata getAttractor_player1_toBad(int wordLen) {
        Automata marked = reachableStateAutomata.get(wordLen);
        if (marked != null){
            //LOGGER.debug("Did map work?: " + marked.prettyPrint("\n--------------\nMark Prev:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
            for(Automata markings: reachableStateAutomata.values()){
                //LOGGER.debug(markings.prettyPrint("markings", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
            }
        }
        if (marked == null) {
            //LOGGER.debug("computing automaton describing reachable configurations of length " + wordLen);

            Map<List<Integer>,Integer> v0_markings = new HashMap<>();
            marked = AutomataUtility.getWordAutomaton(B, wordLen);
            //LOGGER.debug(B.prettyPrint("\n--------------\nPlayer 1 Attractor which can reach Bad:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
           // LOGGER.debug(marked.prettyPrint("\n--------------\n Initially marked words:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
            Automata marked_prev = null;
            int i = 0;
            while(!Automata_equality(marked,marked_prev)){
               // LOGGER.debug("Counter i is at : "  + i);

                i = i+1;
                if (i > 50){
                    break;
                }
                marked_prev = marked;
               // LOGGER.debug(marked_prev.prettyPrint("\n--------------\nMark Prev:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");

                Automata predecessors = VerificationUtility.getPreImage(T,marked);
                Automata predecessors_v0 = AutomataUtility.getIntersection(predecessors, v_0);
                Automata predecessors_v1 = AutomataUtility.minimiseAcyclic(AutomataUtility.getIntersection(predecessors,v_1));
                //LOGGER.debug(predecessors_v1.prettyPrint("\n--------------\nP1 predecessors:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
                // TODO is this right?
                predecessors_v0 = AutomataUtility.minimiseAcyclic(AutomataUtility.getDifference(predecessors_v0,marked));
                List<List<Integer>> v0_predecessor_vertices = AutomataUtility.getWords(predecessors_v0, wordLen);
                //LOGGER.debug(predecessors.prettyPrint("Predecessors", NoInvariantException.getIndexToLabelMapping()));
                /*
                 Save all v0 vertices with amount of successors in a map
                 */
                //LOGGER.debug(" Amount of v0 pred: " + v0_predecessor_vertices.size());
                // TODO Bottleneck in computation
                for(List<Integer> v : v0_predecessor_vertices){
                    if(!v0_markings.containsKey(v)){
                        Automata image_v = VerificationUtility.getImage(v,T,marked.getNumLabels());
                        int n = AutomataUtility.getWords(image_v,wordLen).size();
                       // LOGGER.debug( "predecessor added to v0 markings: " + NoInvariantException.getLabeledWord(v) + "marking: " + n);
                        v0_markings.put(v,n);
                    }
                }
                // Iterate over all saved successors, if n = 0, ignore, otherwise check_p0_marking for them

                for (List<Integer> v0_vertex : v0_markings.keySet()){
                    int n = v0_markings.get(v0_vertex);
                    boolean add_v0 = check_p0_marking(marked, v0_vertex, n, wordLen);
                    if (add_v0){
                        v0_markings.put(v0_vertex,0);
                       // LOGGER.debug( "predecessor added to marked: " + NoInvariantException.getLabeledWord(v0_vertex) + "marking: " + n);
                       // Automata successors = AutomataUtility.minimiseAcyclic(VerificationUtility.getImage(produceWordAutomaton(v0_vertex,I.getNumLabels()),T));
                      //  LOGGER.debug(successors.prettyPrint("\n--------------\nSuccesors of the worda above:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
                        marked = AutomataUtility.getUnion(marked, produceWordAutomaton(v0_vertex, marked.getNumLabels()));
                    }
                }

                marked = AutomataUtility.getUnion(marked, predecessors_v1);
                marked = AutomataUtility.minimiseAcyclic(marked);
              //  LOGGER.debug(marked.prettyPrint("\n--------------\nMarked at End of Loop:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
               // LOGGER.debug("Is marked equals mit marked prev?: " + Automata_equality(marked,marked_prev));
               // LOGGER.debug(marked_prev.prettyPrint("\n--------------\nMark Prev Test:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");


            }

            reachableStateAutomata.put(wordLen, marked);
            //LOGGER.debug(marked.prettyPrint("\n--------------\nPlayer 1 Attractor which can reach Bad:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n" + "for word length: " + wordLen);
            return marked;
        }
        return marked;
    }
    public Automata getAttractor_player1_toState(int wordLen, Automata reach) {
        Automata marked;
        //LOGGER.debug("computing automaton describing reachable configurations of length " + wordLen);
        Map<List<Integer>,Integer> v0_markings = new HashMap<>();
        marked = AutomataUtility.getWordAutomaton(reach, wordLen);
        //LOGGER.debug(B.prettyPrint("\n--------------\nPlayer 1 Attractor which can reach Bad:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
        // LOGGER.debug(marked.prettyPrint("\n--------------\n Initially marked words:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
        Automata marked_prev = null;
        int i = 0;
        while(!Automata_equality(marked,marked_prev)){
            i = i+1;
            if (i > 50){
                break;
            }
            marked_prev = marked;
            //LOGGER.debug(marked_prev.prettyPrint("\n--------------\nP1 can reach Mark Prev:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
            Automata predecessors = VerificationUtility.getPreImage(T,marked);
            Automata predecessors_v0 = AutomataUtility.getIntersection(predecessors, v_0);
            Automata predecessors_v1 = AutomataUtility.getIntersection(predecessors,v_1);
            List<List<Integer>> v0_predecessor_vertices = AutomataUtility.getWords(predecessors_v0, wordLen);
            for(List<Integer> v : v0_predecessor_vertices){
                if(!v0_markings.containsKey(v)){
                    Automata image_v = VerificationUtility.getImage(v,T,marked.getNumLabels());
                    int n = AutomataUtility.getWords(image_v,wordLen).size();
                   /* for (List<Integer> words : AutomataUtility.getWords(image_v,wordLen)){
                        if (k < 4) {
                            LOGGER.debug("P1 can reach  get words: " + NoInvariantException.getLabeledWord(words));
                            k = k +1;
                        }
                    }
                    LOGGER.debug( "P1 can reach predecessor added to v0 markings: " + NoInvariantException.getLabeledWord(v) + "marking: " + n);
                   */
                   v0_markings.put(v,n);
                }
            }
            // Iterate over all saved successors, if n = 0, ignore, otherwise check_p0_marking for them
            for (List<Integer> v0_vertex : v0_markings.keySet()){
                int n = v0_markings.get(v0_vertex);
                boolean add_v0 = check_p0_marking(marked, v0_vertex, n, wordLen);
                if (add_v0){
                    v0_markings.put(v0_vertex,0);
                    marked = AutomataUtility.getUnion(marked, produceWordAutomaton(v0_vertex, marked.getNumLabels()));
                }
            }

            marked = AutomataUtility.getUnion(marked, predecessors_v1);
            marked = AutomataUtility.minimiseAcyclic(marked);
           /* LOGGER.debug(marked.prettyPrint("\n--------------\nP1 can reach Marked at End of Loop:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
            LOGGER.debug("P1 can reach Is marked equals mit marked prev?: " + Automata_equality(marked,marked_prev));
            LOGGER.debug(marked_prev.prettyPrint("\n--------------\nP1 can reach Mark Prev Test:", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
*/

        }
        //LOGGER.debug(marked.prettyPrint("\n--------------\nPlayer 1 can reach::", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");
        return marked;
    }


    public boolean isReachableP1(List<Integer> word)
            throws Timer.TimeoutException {
        if (I.accepts(word)){
            return true;
        }
        // TODO make I finite?
        //LOGGER.debug("Player 0 attractor computation starting");
        Automata attractor_of_word = getAttractor_player1_toState(word.size(), produceWordAutomaton(word, I.getNumLabels()));
        return ((AutomataUtility.getIntersection(I,attractor_of_word)).findAcceptingString() !=null);
    }
    public boolean isReachable(List<Integer> word) throws Timer.TimeoutException{
        return finiteStateSets.isReachable(word);
    }

    public boolean isBadReachable(List<Integer> word){
        String ex = NoInvariantException.getLabeledWord(word);
        //LOGGER.debug("\nPlayer 1 attractor computation starting for: " + ex);
        Automata res = getAttractor_player1_toBad(word.size());
        boolean result =  res.accepts(word);
       // LOGGER.debug(" is bad reachable? : " + result);
        if (result == true){

        }
        return result;
    }
    // TODO produceWord Automaton creates wrong automaton... missing letters!
    public Automata produceWordAutomaton(List<Integer> word, int numLetters){
        Automata result = new Automata(0,word.size()+1,numLetters);
        for(int i = 0; i< word.size(); i++) {
            result.addTrans(i, word.get(i), i + 1);
        }
        Set<Integer> acceptings = new HashSet<Integer>();
        acceptings.add(word.size());
        result.setAcceptingStateIds(acceptings);
        return result;
    }

    private Automata concatenate(Automata a, Automata b){return null;}

    private boolean Automata_equality(Automata a, Automata b){
        if (a == null || b == null){
            return false;
        }
        a = AutomataUtility.toCompleteDFA(a);
        b = AutomataUtility.toCompleteDFA(b);
       // LOGGER.debug(a.prettyPrint("A", NoInvariantException.getIndexToLabelMapping()));

       // LOGGER.debug(b.prettyPrint("B", NoInvariantException.getIndexToLabelMapping()));
        return (AutomataUtility.getIntersection(a,AutomataUtility.getComplement(b)).findAcceptingString() == null);
    }

    /** Method which checks if a vertex can be marked. A  vertex can be marked iff all its successors are accepted
     * by the marked automaton.
     *
     * @param marked Marked automaton are all the states that are backwards reachable already from a starting set
     * @param word The word for which it is checked if it can be marked
     * @param markings How many successors word has
     * @param wordLen The lenght of the word
     * @return True iff vertex can be marked
     */
    private boolean check_p0_marking(Automata marked, List<Integer> word, int markings, int wordLen){
        Automata image_v = VerificationUtility.getImage(word,T,marked.getNumLabels());
        boolean accepted = true;
        for (List<Integer> words : AutomataUtility.getWords(image_v,wordLen)){
            accepted &= marked.accepts(words);
        }
        return accepted;
    }
}


