package theory.fol

trait FOLRules extends FOL {

  @deprecated
  def oops(f: Formula): Theorem = Theorem(f)

  def forall(thm: Theorem)(f: Theorem => Theorem): Theorem = {
    ???
  }

  /** (forall x. y) /\ (forall x. z)  given forall x. y /\ z */
  def ruleForallExtract(thm: Theorem): Theorem = thm.formula match {
    case Forall(named, And(y, z)) => Theorem(And(Forall(named, y), Forall(named, z)))
  }
}
