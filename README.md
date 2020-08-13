# L*-PSynth
L* based Learner for Synthesis of parameterized Systems with safety property
=================================

This file describes how to run the prototype solver.

Currently, the prototype does not provide a user interface and games are given
as .txt files. This means that the desired game has to be selected in the
sources (as described below) and the prototype needs to be executed with the game as input.


Running the prototype
---------------------

There are two ways to run the prototype.

1) execute the .jar File in the repository with a game as an argument. Under windows it  can be done with following command:

    java.exe -jar .\parameterized-learning-master.jar .\SafetyProver\benchmarks-safety-games\nim.txt 

  
2) Use Intellij to create the project SafetyProver and use the Run Configuration Option to set the arguments to the path of the games.

At least Java 8 is needed to compile and run the program.


Encoding of the benchmarks
---------------------
A regular safety game is defined as a tuple (A, I, B) on the arena A = (V0, V1, E) of 
automata, where:
* I represents the set of initial states
* B represents the set of bad states
* V0 represents the Player 0 states (System)
* V1 represents the Player 1 states (Environment)

We illustrate this input format of the tool using a simple example, a parameterized version of the simple take-away game.
There are two players, Player 0 and Player 1 and a pile of 21 chips in the center of the table.
The players take alternating turns removing from one up to three chips at once from the pile.
The player who removes the last chip of the pile is the winner of the game.
Player 0 takes the first turn. In the parameterized versions we look at piles of chips of size 4n and Player 1 is starting.
```
/**
 * The finite automaton defining initial configurations.
 *
 * Here, the first letter "p1" represents the environment is in control of the state.
 * The subsequent ones count the amount of chips on the pile. One 1 corresponds to one chip.
 */
Initial {
    init: si;

    si -> s0 p1;
    s0 -> s1 1;
    s1 -> s2 1;
    s2 -> s3 1;
    s3 -> s0 1;
    accepting: s0, sn;
}       

/**
 * The transition relation of the take-away game.
 * The first bit changes in each step to alternate between Player 0 and Player 1. If the first bit is p0, then the state belongs to Player 0.
 * Afterwards, 1 to 3 chips can be removed from the pile. 
 * To avoid being the game finite duration, an endless loop when the pile is empty is added which 
 * just alternates between players.
 */
 
Transition {
    init: si;

    // Empty P0
    si -> sk p0/p1;
    si -> sk p1/p0;

    si -> sd p1/p0;
    si -> sd p0/p1;
    sd1 -> sd1 0/0;
    sd -> sd1 0/1;
    sk -> sk 1/1;
    sn -> sn 0/0;

    sk -> sn 1/0;
    sk -> s2 1/0;
    sk -> s1 1/0;

    s1 -> s2 1/0;
    s2 -> sn 1/0;
    accepting: sn,sd,sd1;  

}

/**
 * The finite automaton defining bad configurations.
 * A bad state is reached if it is Player 0 has to take a turn and the pile is empty.
 */
Bad {
    init: s0;

    s0 -> s1 p0;
    s1 -> s2 0;
    s2 -> s2 0;
 
    accepting: s2;
}

/**
 * The finite automaton defining Player 0 configurations.
 * A state belongs to Player 0 if and only if the word encoding it starts with p0.
 */
P0 {
    init: si;

    si -> s0 p0;
    s0 -> s1 1;
    s1 -> s1 1;
    s0 -> s2 0;
    s1 -> s2 0;
    s2 -> s2 0;

    accepting: s1,s2;

}

/**
 * The finite automaton defining Player 1 configurations.
 * A state belongs to Player 1 if and only if the word encoding it starts with p1.
 */
P1 {
    init: si;

    si -> s0 p0;
    s0 -> s1 1;
    s1 -> s1 1;
    s0 -> s2 0;
    s1 -> s2 0;
    s2 -> s2 0;

    accepting: s1,s2;

}
