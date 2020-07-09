package learning;

import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;

public abstract class SafetyGameTeacher extends Teacher {
    private final Automata I;
    private final Automata v_0;
    private final Automata v_1;
    private final Automata B;
    private final EdgeWeightedDigraph T;

    public SafetyGameTeacher(int numLetters, Automata I, Automata B, Automata v_0, Automata v_1, EdgeWeightedDigraph T) {
        super(numLetters);
        this.I = I;
        this.v_0 = v_0;
        this.v_1 = v_1;
        this.B = B;
        this.T = T;
    }

    public Automata getInitialStates() {
        return I;
    }

    public Automata getBadStates() {
        return B;
    }

    public Automata getPlayer0_vertices(){return v_0;}

    public Automata getPlayer1_vertices(){return v_1;}

    public EdgeWeightedDigraph getTransition() {
        return T;
    }
}
