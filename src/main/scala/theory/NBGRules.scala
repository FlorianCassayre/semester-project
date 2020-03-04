package theory

trait NBGRules extends NBGTheory {

  /** `(x = y) <-> (forall z. z in x <-> z in y)` */
  def equalsIff[X <: AnySet, Y <: AnySet](x: X, y: Y, id: Id): Theorem[(X === Y) <-> Forall[SetVariable, Member[SetVariable, X] <-> Member[SetVariable, Y]]] = {
    val z = SetVariable(id)
    Theorem((x === y) <-> Forall(z, (z in x) <-> (z in y)))
  }

  /** (x sube y) <-> (forall z. z in x -> z in y) */
  def subsetEqIff[X <: AnySet, Y <: AnySet](x: X, y: Y, id: Id): Theorem[SubsetEqual[X, Y] <-> Forall[SetVariable, Member[SetVariable, X] ->: Member[SetVariable, Y]]] = {
    val z = SetVariable(id)
    Theorem((x sube y) <-> Forall(z, (z in x) ->: (z in y)))
  }

  /** (x sub y) <-> (x sube y /\ x != y) */
  def subsetStrictIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetStrict[X, Y] <-> (SubsetEqual[X, Y] /\ ~[X === Y])] =
    Theorem((x sub y) <-> ((x sube y) /\ ~(x === y)))

  /** M(x) <-> exists y. x in y */
  /*def defIsSet[X <: AnySet, Y <: AnySet](x: X, id: Id): Theorem = {
    val y = SetVariable(id)
    Theorem(IsSet(x) <-> Exists(y, x in y))
  }*/

  /** Pr(x) <-> ~M(x) */
  /*def defIsClass(x: AnySet): Theorem =
    Theorem(IsClass(x) <-> ~IsSet(x))*/

  // --

  /*def axiomP(x: AnySet, y: AnySet): Theorem = {
    val pair = PairSet(x, y)
    Theorem((x in pair) /\ (y in pair))
  }*/

  /*def axiomN(x: AnySet): Theorem = Theorem(~(x in EmptySet))*/

  /** forall u. (u in (x inter y)) <-> ((u in x) /\ (u in y)) */
  def intersectIff[X <: AnySet, Y <: AnySet](x: X, y: Y, id: Id): Theorem[Forall[SetVariable, Member[SetVariable, Intersect[X, Y]] <-> (Member[SetVariable, X] /\ Member[SetVariable, Y])]] = {
    val u = SetVariable(id)
    Theorem(Forall(u, (u in (x inter y)) <-> ((u in x) /\ (u in y))))
  }


}
