package theory

trait NBGRules extends NBGTheory {

  type FA = "a"
  type FB = "b"

  /** `(x = y) -> (z in x <-> z in y)` */
  def equalsIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[Z, X] <-> Member[Z, Y])] =
    Theorem((x === y) ->: ((z in x) <-> (z in y)))

  /** `(a(x, y) in x <-> a(x, y) in y) -> (x = y)` */
  def equalsIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FA, X, Y], X] <-> Member[SkolemFunction2[FA, X, Y], Y]) ->: (X === Y)] = {
    val a = SkolemFunction2[FA, X, Y](x, y)
    Theorem(((a in x) <-> (a in y)) ->: (x === y))
  }

  /** (x sube y) -> (z in x -> z in y) */
  def subsetEqIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[SubsetEqual[X, Y] ->: (Member[Z, X] ->: Member[Z, Y])] =
    Theorem((x sube y) ->: ((z in x) ->: (z in y)))

  /** (b(x, y) in x -> b(x, y) in y) -> (x sube y) */
  def subsetEqIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FB, X, Y], X] ->: Member[SkolemFunction2[FB, X, Y], Y]) ->: SubsetEqual[X, Y]] = {
    val b = SkolemFunction2[FB, X, Y](x, y)
    Theorem(((b in x) ->: (b in y)) ->: (x sube y))
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

  /** z in (x inter y)) <-> ((z in x) /\ (z in y)) */
  def intersectIff[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Member[Z, Intersect[X, Y]] <-> (Member[Z, X] /\ Member[Z, Y])] =
    Theorem((z in (x inter y)) <-> ((z in x) /\ (z in y)))

}
