package theory

trait NBGRules extends NBGTheory {

  /** `(x = y) <-> (forall z. z in x <-> z in y)` */
  def equalsIff(x: AnySet, y: AnySet, id: Id): Theorem = {
    val z = SetVariable(id)
    Theorem((x === y) <-> Forall(z, (z in x) <-> (z in y)))
  }

  /** (x subseteq y) <-> (forall z. z in x -> z in y) */
  def inclusionEqForall(x: AnySet, y: AnySet, id: Id): Theorem = {
    val z = SetVariable(id)
    Theorem(Iff(SubsetEqual(x, y), Forall(z, Implies(Member(z, x), Member(z, y)))))
  }

  /** (x subset y) <-> (x subseteq y /\ x != y) */
  def inclusionForall(x: AnySet, y: AnySet): Theorem =
    Theorem(Iff(SubsetStrict(x, y), And(SubsetEqual(x, y), Not(Equals(x, y)))))

  /**  */




  /** M(x) <-> exists y. x in y */
  def defIsSet(x: AnySet, id: Id): Theorem = {
    val y = SetVariable(id)
    Theorem(Iff(IsSet(x), Exists(y, Member(x, y))))
  }

  /** Pr(x) <-> ~M(x) */
  def defIsClass(x: AnySet): Theorem =
    Theorem(Iff(IsClass(x), Not(IsSet(x))))

  // --

  /** (forall z. z in x <-> z in y) given x = y */
  def ruleEqForall(thm: Theorem, id: Id): Theorem = thm.formula match {
    case Equals(x, y) => equalsIff(x, y, id)
  }

  def ruleForallEq(thm: Theorem): Theorem = thm.formula match {
    case Forall(SetVariable(v0), Iff(Member(SetVariable(v1), x), Member(SetVariable(v2), y))) if v0 == v1 && v0 == v2 =>
      Theorem(Equals(x, y))
  }



  def axiomP(x: AnySet, y: AnySet): Theorem = {
    val pair = PairSet(x, y)
    Theorem(And(Member(x, pair), Member(y, pair)))
  }

  def axiomN(x: AnySet): Theorem = Theorem(Not(Member(x, EmptySet)))


}
