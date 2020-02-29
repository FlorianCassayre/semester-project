package theory

trait NBGTheorems extends NBGRules {

  /** x subseteq y /\ y subseteq x given x = y */
  def ruleEqualitySubset(thm: Theorem): Theorem = thm.formula match {
    case Equals(x, y) =>
      val id = fresh()
      forall(ruleEqForall(thm, id)) { t =>
        ruleIffAndImplies(t)
      } // FIXME
  }

  /** x = x */
  def equalsReflexive(x: AnySet): Theorem = {
    val id = fresh()
    val z = SetVariable(id)
    toImplies(iffCommutative(equalsIff(x, x, id)))(generalize(iffReflexive(z in x), z))
  }

  /** x = y -> y = x */
  def equalsSym(x: AnySet, y: AnySet): Theorem = ???



  /** x in y -> M(x) */
  def inclusionIsSet(x: AnySet, y: AnySet): Theorem = ???


}
