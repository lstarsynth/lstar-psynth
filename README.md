# L*-PSynth
L* based Learner for Synthesis of parameterized Systems with safety property
=================================

This file describes how to and run the prototype solver.

Currently, the prototype does not provide a user interface and games are given
as .txt files. This means that the desired game has to be selected in the
sources (as described below) and the prototype needs to be executed with the game as input.


Running the prototype
---------------------

There are two ways to run the prototype.

1) execute the .jar File in the repository with a game as an argument. Under windows it  can be done with following command:

    java.exe -jar .\parameterized-learning-master.jar .\SafetyProver\benchmarks-safety-games\nim.txt 

  
2) Use Intellij to create the project SafetyProver and use the Run Configuration Option to set the arguments to the path of the games.

