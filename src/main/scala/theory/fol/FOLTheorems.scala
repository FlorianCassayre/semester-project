package theory.fol

trait FOLTheorems extends FOLRules {

  /** y /\ x given x /\ y */
  def ruleAndCommutativity(thm: Theorem): Theorem = thm.formula match {
    case And(x, y) => ???
  }

  /** x -> y /\ y -> x given x <-> y */
  def ruleIffAndImplies(thm: Theorem): Theorem = thm.formula match {
    case Iff(x, y) => ???
  }

}
