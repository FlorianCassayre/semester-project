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
    Theorem((x sube y) <-> Forall(z, (z in x) ->: (z in y)))
  }

  /** (x sub y) <-> (x sube y /\ x != y) */
  def subsetStrictIff(x: AnySet, y: AnySet): Theorem =
    Theorem((x sub y) <-> ((x sube y) /\ ~(x === y)))

  /** M(x) <-> exists y. x in y */
  def defIsSet(x: AnySet, id: Id): Theorem = {
    val y = SetVariable(id)
    Theorem(IsSet(x) <-> Exists(y, x in y))
  }

  /** Pr(x) <-> ~M(x) */
  def defIsClass(x: AnySet): Theorem =
    Theorem(IsClass(x) <-> ~IsSet(x))

  // --

  def axiomP(x: AnySet, y: AnySet): Theorem = {
    val pair = PairSet(x, y)
    Theorem((x in pair) /\ (y in pair))
  }

  def axiomN(x: AnySet): Theorem = Theorem(~(x in EmptySet))


}
