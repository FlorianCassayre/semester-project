package theory

trait NBGRules extends NBGTheory {

  /** `(x = y) <-> (forall z. z in x <-> z in y)` */
  def equalsIff(x: AnySet, y: AnySet, id: Id): Theorem = {
    val z = SetVariable(id)
    Theorem((x === y) <-> Forall(z, (z in x) <-> (z in y)))
  }

  /** (x sube y) <-> (forall z. z in x -> z in y) */
  def subsetEqIff(x: AnySet, y: AnySet, id: Id): Theorem = {
    val z = SetVariable(id)
    Theorem(Iff(SubsetEqual(x, y), Forall(z, Implies(Member(z, x), Member(z, y)))))
  }

  /** (x sub y) <-> (x sube y /\ x != y) */
  def subsetStrictIff(x: AnySet, y: AnySet): Theorem =
    Theorem(Iff(SubsetStrict(x, y), And(SubsetEqual(x, y), Not(Equals(x, y)))))

  /** M(x) <-> exists y. x in y */
  def defIsSet(x: AnySet, id: Id): Theorem = {
    val y = SetVariable(id)
    Theorem(Iff(IsSet(x), Exists(y, Member(x, y))))
  }

  /** Pr(x) <-> ~M(x) */
  def defIsClass(x: AnySet): Theorem =
    Theorem(Iff(IsClass(x), Not(IsSet(x))))

  // --

  def axiomP(x: AnySet, y: AnySet): Theorem = {
    val pair = PairSet(x, y)
    Theorem(And(Member(x, pair), Member(y, pair)))
  }

  def axiomN(x: AnySet): Theorem = Theorem(Not(Member(x, EmptySet)))


}
