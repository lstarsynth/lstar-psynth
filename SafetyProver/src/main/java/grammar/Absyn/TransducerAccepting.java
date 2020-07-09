package grammar.Absyn; // Java Package generated by the BNF Converter.

public class TransducerAccepting extends AcceptingRule {
  public final ListName listname_;
  public TransducerAccepting(ListName p1) { listname_ = p1; }

  public <R,A> R accept(grammar.Absyn.AcceptingRule.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(Object o) {
    if (this == o) return true;
    if (o instanceof grammar.Absyn.TransducerAccepting) {
      grammar.Absyn.TransducerAccepting x = (grammar.Absyn.TransducerAccepting)o;
      return this.listname_.equals(x.listname_);
    }
    return false;
  }

  public int hashCode() {
    return this.listname_.hashCode();
  }


}
