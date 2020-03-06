package theory

trait NBGRules extends NBGTheory {

  type FA = "a"
  type FB = "b"
  type FC = "c"

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

  /** M(x) -> (x in c(x)) */
  def isSetIff1[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, SkolemFunction1[FC, X]]] =
    Theorem(IsSet(x) ->: (x in SkolemFunction1[FC, X](x)))

  /** (x in y) -> M(x) */
  def isSetIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Member[X, Y] ->: IsSet[X]] =
    Theorem((x in y) ->: IsSet(x))

  // --

  /** (x = y) <-> ((x in z) <-> (y in z)) */
  def axiomT[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[X, Z] <-> Member[Y, Z])] =
    Theorem((x === y) ->: ((x in z) <-> (y in z)))

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
