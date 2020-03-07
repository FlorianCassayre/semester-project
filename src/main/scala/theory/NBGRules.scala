package theory

trait NBGRules extends NBGTheory {

  /** `(x = y) -> (z in x <-> z in y)` */
  def equalsIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[Z, X] <-> Member[Z, Y])] =
    Theorem((x === y) ->: ((z in x) <-> (z in y)))

  type FA = "a"
  /** `M(a(x, y))` */
  def isSetFa[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[SkolemFunction2[FA, X, Y]]] = Theorem(IsSet(SkolemFunction2(x, y)))

  /** `(a(x, y) in x <-> a(x, y) in y) -> (x = y)` */
  def equalsIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FA, X, Y], X] <-> Member[SkolemFunction2[FA, X, Y], Y]) ->: (X === Y)] = {
    val a = SkolemFunction2[FA, X, Y](x, y)
    Theorem(((a in x) <-> (a in y)) ->: (x === y))
  }

  /** (x sube y) -> (z in x -> z in y) */
  def subsetEqIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[SubsetEqual[X, Y] ->: (Member[Z, X] ->: Member[Z, Y])] =
    Theorem((x sube y) ->: ((z in x) ->: (z in y)))

  type FB = "b"
  /** (b(x, y) in x -> b(x, y) in y) -> (x sube y) */
  def subsetEqIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FB, X, Y], X] ->: Member[SkolemFunction2[FB, X, Y], Y]) ->: SubsetEqual[X, Y]] = {
    val b = SkolemFunction2[FB, X, Y](x, y)
    Theorem(((b in x) ->: (b in y)) ->: (x sube y))
  }

  /** (x sub y) <-> (x sube y /\ x != y) */
  def subsetStrictIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetStrict[X, Y] <-> (SubsetEqual[X, Y] /\ ~[X === Y])] =
    Theorem((x sub y) <-> ((x sube y) /\ ~(x === y)))

  type FC = "c"
  /** M(x) -> (x in c(x)) */
  def isSetIff1[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, SkolemFunction1[FC, X]]] =
    Theorem(IsSet(x) ->: (x in SkolemFunction1[FC, X](x)))

  /** (x in y) -> M(x) */
  def isSetIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Member[X, Y] ->: IsSet[X]] =
    Theorem((x in y) ->: IsSet(x))

  /** {x} = {x, x} */
  def singletonIff[X <: AnySet](x: X): Theorem[SingletonSet[X] === PairSet[X, X]] =
    Theorem(SingletonSet(x) === PairSet(x, x))

  // --

  /** `(x = y) <-> ((x in z) <-> (y in z))` */
  def axiomT[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[X, Z] <-> Member[Y, Z])] =
    Theorem((x === y) ->: ((x in z) <-> (y in z)))

  /** `M(x) -> M(y) -> M(z) -> ((z in {x, y}) <-> (z = x \/ z = y))` */
  def axiomP[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[X] ->: IsSet[Y] ->: IsSet[Z] ->: (Member[Z, PairSet[X, Y]] <-> ((Z === X) \/ (Z === Y)))] =
    Theorem(IsSet(x) ->: IsSet(y) ->: IsSet(z) ->: ((z in PairSet(x, y)) <-> ((z === x) \/ (z === y))))

  /** `M(x) -> ~(x in {})` */
  def axiomN[X <: AnySet](x: X): Theorem[IsSet[X] ->: ~[Member[X, EmptySet]]] = Theorem(IsSet(x) ->: ~(x in EmptySet))

  // --

  /** z in (x inter y)) <-> ((z in x) /\ (z in y)) */
  def intersectIff[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Member[Z, Intersect[X, Y]] <-> (Member[Z, X] /\ Member[Z, Y])] =
    Theorem((z in (x inter y)) <-> ((z in x) /\ (z in y)))

}
