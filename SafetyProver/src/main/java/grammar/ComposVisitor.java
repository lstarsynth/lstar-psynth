package grammar;
import grammar.Absyn.*;
/** BNFC-Generated Composition Visitor
*/

public class ComposVisitor<A> implements
  grammar.Absyn.ModelRule.Visitor<grammar.Absyn.ModelRule,A>,
  grammar.Absyn.TransducerRule.Visitor<grammar.Absyn.TransducerRule,A>,
  grammar.Absyn.InitRule.Visitor<grammar.Absyn.InitRule,A>,
  grammar.Absyn.TransitionRule.Visitor<grammar.Absyn.TransitionRule,A>,
  grammar.Absyn.AcceptingRule.Visitor<grammar.Absyn.AcceptingRule,A>,
  grammar.Absyn.AutomatonRule.Visitor<grammar.Absyn.AutomatonRule,A>,
  grammar.Absyn.AutomataInitRule.Visitor<grammar.Absyn.AutomataInitRule,A>,
  grammar.Absyn.AutomataTransitionRule.Visitor<grammar.Absyn.AutomataTransitionRule,A>,
  grammar.Absyn.AutomataAcceptingsRule.Visitor<grammar.Absyn.AutomataAcceptingsRule,A>,
  grammar.Absyn.VerifierOption.Visitor<grammar.Absyn.VerifierOption,A>,
  grammar.Absyn.SymmetryOption.Visitor<grammar.Absyn.SymmetryOption,A>,
  grammar.Absyn.MaybeClosed.Visitor<grammar.Absyn.MaybeClosed,A>,
  grammar.Absyn.Name.Visitor<grammar.Absyn.Name,A>
{
/* ModelRule */
    public ModelRule visit(grammar.Absyn.Model p, A arg)
    {
      AutomatonRule automatonrule_1 = p.automatonrule_1.accept(this, arg);
      MaybeClosed maybeclosed_ = p.maybeclosed_.accept(this, arg);
      TransducerRule transducerrule_ = p.transducerrule_.accept(this, arg);
      AutomatonRule automatonrule_2 = p.automatonrule_2.accept(this, arg);
      AutomatonRule automatonrule_3 = p.automatonrule_3.accept(this, arg);
      AutomatonRule automatonrule_4 = p.automatonrule_4.accept(this, arg);
      ListVerifierOption listverifieroption_ = new ListVerifierOption();
      for (VerifierOption x : p.listverifieroption_)
      {
        listverifieroption_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.Model(automatonrule_1, maybeclosed_, transducerrule_, automatonrule_2, automatonrule_3, automatonrule_4, listverifieroption_);
    }
/* TransducerRule */
    public TransducerRule visit(grammar.Absyn.Transducer p, A arg)
    {
      InitRule initrule_ = p.initrule_.accept(this, arg);
      ListTransitionRule listtransitionrule_ = new ListTransitionRule();
      for (TransitionRule x : p.listtransitionrule_)
      {
        listtransitionrule_.add(x.accept(this,arg));
      }
      AcceptingRule acceptingrule_ = p.acceptingrule_.accept(this, arg);
      return new grammar.Absyn.Transducer(initrule_, listtransitionrule_, acceptingrule_);
    }
/* InitRule */
    public InitRule visit(grammar.Absyn.TransducerInitialState p, A arg)
    {
      Name name_ = p.name_.accept(this, arg);
      return new grammar.Absyn.TransducerInitialState(name_);
    }
/* TransitionRule */
    public TransitionRule visit(grammar.Absyn.FulTransition p, A arg)
    {
      Name name_1 = p.name_1.accept(this, arg);
      Name name_2 = p.name_2.accept(this, arg);
      Name name_3 = p.name_3.accept(this, arg);
      Name name_4 = p.name_4.accept(this, arg);
      return new grammar.Absyn.FulTransition(name_1, name_2, name_3, name_4);
    }    public TransitionRule visit(grammar.Absyn.EmptyTransition p, A arg)
    {
      Name name_1 = p.name_1.accept(this, arg);
      Name name_2 = p.name_2.accept(this, arg);
      return new grammar.Absyn.EmptyTransition(name_1, name_2);
    }    public TransitionRule visit(grammar.Absyn.LoopingTransition p, A arg)
    {
      ListName listname_ = new ListName();
      for (Name x : p.listname_)
      {
        listname_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.LoopingTransition(listname_);
    }
/* AcceptingRule */
    public AcceptingRule visit(grammar.Absyn.TransducerAccepting p, A arg)
    {
      ListName listname_ = new ListName();
      for (Name x : p.listname_)
      {
        listname_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.TransducerAccepting(listname_);
    }
/* AutomatonRule */
    public AutomatonRule visit(grammar.Absyn.Automaton p, A arg)
    {
      AutomataInitRule automatainitrule_ = p.automatainitrule_.accept(this, arg);
      ListAutomataTransitionRule listautomatatransitionrule_ = new ListAutomataTransitionRule();
      for (AutomataTransitionRule x : p.listautomatatransitionrule_)
      {
        listautomatatransitionrule_.add(x.accept(this,arg));
      }
      AutomataAcceptingsRule automataacceptingsrule_ = p.automataacceptingsrule_.accept(this, arg);
      return new grammar.Absyn.Automaton(automatainitrule_, listautomatatransitionrule_, automataacceptingsrule_);
    }
/* AutomataInitRule */
    public AutomataInitRule visit(grammar.Absyn.AutomataInitialState p, A arg)
    {
      Name name_ = p.name_.accept(this, arg);
      return new grammar.Absyn.AutomataInitialState(name_);
    }
/* AutomataTransitionRule */
    public AutomataTransitionRule visit(grammar.Absyn.AutomataTransition p, A arg)
    {
      Name name_1 = p.name_1.accept(this, arg);
      Name name_2 = p.name_2.accept(this, arg);
      Name name_3 = p.name_3.accept(this, arg);
      return new grammar.Absyn.AutomataTransition(name_1, name_2, name_3);
    }    public AutomataTransitionRule visit(grammar.Absyn.AutomataEmptyTransition p, A arg)
    {
      Name name_1 = p.name_1.accept(this, arg);
      Name name_2 = p.name_2.accept(this, arg);
      return new grammar.Absyn.AutomataEmptyTransition(name_1, name_2);
    }
/* AutomataAcceptingsRule */
    public AutomataAcceptingsRule visit(grammar.Absyn.AutomataAcceptings p, A arg)
    {
      ListName listname_ = new ListName();
      for (Name x : p.listname_)
      {
        listname_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.AutomataAcceptings(listname_);
    }
/* VerifierOption */
    public VerifierOption visit(grammar.Absyn.NumOfStatesTransducerGuess p, A arg)
    {
      String myinteger_1 = p.myinteger_1;
      String myinteger_2 = p.myinteger_2;
      return new grammar.Absyn.NumOfStatesTransducerGuess(myinteger_1, myinteger_2);
    }    public VerifierOption visit(grammar.Absyn.NumOfStatesAutomatonGuess p, A arg)
    {
      String myinteger_1 = p.myinteger_1;
      String myinteger_2 = p.myinteger_2;
      return new grammar.Absyn.NumOfStatesAutomatonGuess(myinteger_1, myinteger_2);
    }    public VerifierOption visit(grammar.Absyn.NumOfInitStatesAutomatonGuess p, A arg)
    {
      String myinteger_1 = p.myinteger_1;
      String myinteger_2 = p.myinteger_2;
      return new grammar.Absyn.NumOfInitStatesAutomatonGuess(myinteger_1, myinteger_2);
    }    public VerifierOption visit(grammar.Absyn.SymmetryOptions p, A arg)
    {
      ListSymmetryOption listsymmetryoption_ = new ListSymmetryOption();
      for (SymmetryOption x : p.listsymmetryoption_)
      {
        listsymmetryoption_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.SymmetryOptions(listsymmetryoption_);
    }    public VerifierOption visit(grammar.Absyn.ExplicitChecks p, A arg)
    {
      String myinteger_ = p.myinteger_;
      return new grammar.Absyn.ExplicitChecks(myinteger_);
    }    public VerifierOption visit(grammar.Absyn.UseRankingFunctions p, A arg)
    {
      return new grammar.Absyn.UseRankingFunctions();
    }    public VerifierOption visit(grammar.Absyn.MonolithicWitness p, A arg)
    {
      return new grammar.Absyn.MonolithicWitness();
    }    public VerifierOption visit(grammar.Absyn.NoPrecomputedInv p, A arg)
    {
      return new grammar.Absyn.NoPrecomputedInv();
    }    public VerifierOption visit(grammar.Absyn.LogLevel p, A arg)
    {
      String myinteger_ = p.myinteger_;
      return new grammar.Absyn.LogLevel(myinteger_);
    }    public VerifierOption visit(grammar.Absyn.ParLevel p, A arg)
    {
      String myinteger_ = p.myinteger_;
      return new grammar.Absyn.ParLevel(myinteger_);
    }
/* SymmetryOption */
    public SymmetryOption visit(grammar.Absyn.RotationSymmetry p, A arg)
    {
      return new grammar.Absyn.RotationSymmetry();
    }    public SymmetryOption visit(grammar.Absyn.RotationWithSymmetry p, A arg)
    {
      ListName listname_ = new ListName();
      for (Name x : p.listname_)
      {
        listname_.add(x.accept(this,arg));
      }
      return new grammar.Absyn.RotationWithSymmetry(listname_);
    }
/* MaybeClosed */
    public MaybeClosed visit(grammar.Absyn.ClosedInit p, A arg)
    {
      return new grammar.Absyn.ClosedInit();
    }    public MaybeClosed visit(grammar.Absyn.NotClosedInit p, A arg)
    {
      return new grammar.Absyn.NotClosedInit();
    }
/* Name */
    public Name visit(grammar.Absyn.NumberName p, A arg)
    {
      String myinteger_ = p.myinteger_;
      return new grammar.Absyn.NumberName(myinteger_);
    }    public Name visit(grammar.Absyn.LiteralName p, A arg)
    {
      String labelident_ = p.labelident_;
      return new grammar.Absyn.LiteralName(labelident_);
    }
}