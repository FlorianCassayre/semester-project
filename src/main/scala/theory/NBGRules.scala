package theory

import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._
import theory.NBGTheory._

object NBGRules {

  // Equality and sets

  /** `(x = y) -> (z in x <-> z in y)` */
  def equalsIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[Z, X] <-> Member[Z, Y])] =
    Axiom((x === y) ->: ((z in x) <-> (z in y)))

  type FA = "a"
  /** `M(a(x, y))` */
  def isSetFa[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[SkolemFunction2[FA, X, Y]]] = Axiom(IsSet(SkolemFunction2(x, y)))

  /** `(a(x, y) in x <-> a(x, y) in y) -> (x = y)` */
  def equalsIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FA, X, Y], X] <-> Member[SkolemFunction2[FA, X, Y], Y]) ->: (X === Y)] = {
    val a = SkolemFunction2[FA, X, Y](x, y)
    Axiom(((a in x) <-> (a in y)) ->: (x === y))
  }

  /** `(x sube y) -> (z in x -> z in y)` */
  def subsetEqIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[SubsetEqual[X, Y] ->: (Member[Z, X] ->: Member[Z, Y])] =
    Axiom((x sube y) ->: ((z in x) ->: (z in y)))

  type FB = "b"
  /** `M(b(x, y))` */
  def isSetFb[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[SkolemFunction2[FB, X, Y]]] = Axiom(IsSet(SkolemFunction2[FB, X, Y](x, y)))

  /** `(b(x, y) in x -> b(x, y) in y) -> (x sube y)` */
  def subsetEqIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(Member[SkolemFunction2[FB, X, Y], X] ->: Member[SkolemFunction2[FB, X, Y], Y]) ->: SubsetEqual[X, Y]] = {
    val b = SkolemFunction2[FB, X, Y](x, y)
    Axiom(((b in x) ->: (b in y)) ->: (x sube y))
  }

  /** `(x sub y) <-> (x sube y /\ x != y)` */
  def subsetStrictIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetStrict[X, Y] <-> (SubsetEqual[X, Y] /\ ~[X === Y])] =
    Axiom((x sub y) <-> ((x sube y) /\ ~(x === y)))

  type FC = "c"
  /** `M(x) -> (x in c(x))` */
  def isSetIff1[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, SkolemFunction1[FC, X]]] =
    Axiom(IsSet(x) ->: (x in SkolemFunction1[FC, X](x)))

  /** `(x in y) -> M(x)` */
  def isSetIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Member[X, Y] ->: IsSet[X]] =
    Axiom((x in y) ->: IsSet(x))

  // Axioms

  /** `(x = y) -> ((x in z) <-> (y in z))` */
  def axiomT[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[(X === Y) ->: (Member[X, Z] <-> Member[Y, Z])] =
    Axiom((x === y) ->: ((x in z) <-> (y in z)))

  /** `M(x) -> M(y) -> M(z) -> ((z in {x, y}) <-> (z = x \/ z = y))` */
  def axiomP[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[X] ->: IsSet[Y] ->: IsSet[Z] ->: (Member[Z, PairSet[X, Y]] <-> ((Z === X) \/ (Z === Y)))] =
    Axiom(IsSet(x) ->: IsSet(y) ->: IsSet(z) ->: ((z in PairSet(x, y)) <-> ((z === x) \/ (z === y))))

  /** `M(x) -> M(y) -> M({x, y})` */
  def axiomPS[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: IsSet[PairSet[X, Y]]] =
    Axiom(IsSet(x) ->: IsSet(y) ->: IsSet(PairSet(x, y)))

  /** `M(x) -> ~(x in {})` */
  def axiomN[X <: AnySet](x: X): Theorem[IsSet[X] ->: ~[Member[X, EmptySet]]] = Axiom(IsSet(x) ->: ~(x in EmptySet))

  /** `M({})` */
  def axiomNS: Theorem[IsSet[EmptySet]] = Axiom(IsSet(EmptySet))

  /** `M(x) -> M(y) -> ((<x, y> in d) <-> (x in y))` */
  def memberRelationIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[OrderedPair[X, Y], MemberRelation] <-> Member[X, Y])] =
    Axiom(IsSet(x) ->: IsSet(y) ->: ((OrderedPair(x, y) in MemberRelation) <-> (x in y)))

  /** `M(z) -> (z in (x inter y)) <-> ((z in x) /\ (z in y))` */
  def intersectIff[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Z] ->: (Member[Z, Intersect[X, Y]] <-> (Member[Z, X] /\ Member[Z, Y]))] =
    Axiom(IsSet(z) ->: ((z in (x inter y)) <-> ((z in x) /\ (z in y))))

  /** `M(y) -> ((y in -x) <-> ~(y in x)` */
  def complementIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[Y] ->: (Member[Y, -[X]] <-> ~[Member[Y, X]])] =
    Axiom(IsSet(y) ->: ((y in -x) <-> ~(y in x)))

  /** `M(y) -> M(z) -> ((<y, z> in x) -> (y in D(x)))` */
  def domainIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Y] ->: IsSet[Z] ->: Member[OrderedPair[Y, Z], X] ->: Member[Y, Domain[X]]] =
    Axiom(IsSet(y) ->: IsSet(z) ->: (OrderedPair(y, z) in x) ->: (y in Domain(x)))

  type FE = "e"
  /** `M(e(x, y))` */
  def isSetFe[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[SkolemFunction2[FE, X, Y]]] = Axiom(IsSet(SkolemFunction2(x, y)))

  /** `M(y) -> ((y in D(x)) -> (<y, e(x, y)> in x))` */
  def domainIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[Y] ->: Member[Y, Domain[X]] ->: Member[OrderedPair[Y, SkolemFunction2[FE, X, Y]], X]] =
    Axiom(IsSet(y) ->: (y in Domain(x)) ->: (OrderedPair(y, SkolemFunction2[FE, X, Y](x, y)) in x))

  type FU = "u"
  def isSetU[X <: AnySet](x: X): Theorem[IsSet[SkolemFunction1[FU, X]]] = Axiom(IsSet(SkolemFunction1[FU, X](x)))

  /** `(<u, v> in f(x)) <-> (u in x)` */
  def axiomB5[X <: AnySet, U <: AnySet, V <: AnySet](x: X, u: U, v: V): Theorem[Member[OrderedPair[U, V], SkolemFunction1[FU, X]] <-> Member[U, X]] =
    Axiom((OrderedPair(u, v) in SkolemFunction1[FU, X](x)) <-> (u in x))

  // TODO B*

  /** `M(x) -> M(U(x))` */
  def axiomU[X <: AnySet](x: X): Theorem[IsSet[X] ->: IsSet[Sum[X]]] = Axiom(IsSet(x) ->: IsSet(Sum(x)))

  /** `M(x) -> M(P(x))` */
  def axiomW[X <: AnySet](x: X): Theorem[IsSet[X] ->: IsSet[Power[X]]] = Axiom(IsSet(x) ->: IsSet(Power(x)))

  type FM = "m"
  type FN = "n"
  def isSetM[F <: AnySet, X <: AnySet](f: F, x: X): Theorem[IsSet[SkolemFunction2[FM, F, X]]] = Axiom(IsSet(SkolemFunction2(f, x)))
  def isSetN[F <: AnySet, X <: AnySet, U <: AnySet](f: F, x: X, u: U): Theorem[IsSet[SkolemFunction3[FN, F, X, U]]] = Axiom(IsSet(SkolemFunction3(f, x, u)))

  /** `Fnc(f) -> M(x) -> M(u) -> (u in m(f, x)) -> ((<n(f, x, u), u> in f) /\ (n(f, x, u) in x))` */
  def axiomR1[F <: AnySet, X <: AnySet, U <: AnySet](f: F, x: X, u: U):
  Theorem[Fnc[F] ->: IsSet[X] ->: IsSet[U] ->: (Member[U, SkolemFunction2[FM, F, X]] ->: (Member[OrderedPair[SkolemFunction3[FN, F, X, U], U], F] /\ Member[SkolemFunction3[FN, F, X, U], X]))] = {
    val m = SkolemFunction2[FM, F, X](f, x)
    val n = SkolemFunction3[FN, F, X, U](f, x, u)
    Axiom(Fnc(f) ->: IsSet(x) ->: IsSet(u) ->: ((u in m) ->: ((OrderedPair(n, u) in f) /\ (n in x))))
  }

  /** `Fnc(f) -> M(x) -> M(v) -> ((<v, u> in f) /\ (v in x))) -> (u in m(f, x))` */
  def axiomR2[F <: AnySet, X <: AnySet, U <: AnySet, V <: AnySet](f: F, x: X, u: U, v: V):
  Theorem[Fnc[F] ->: IsSet[X] ->: IsSet[V] ->: (Member[OrderedPair[V, U], F] /\ Member[V, X]) ->: Member[U, SkolemFunction2[FM, F, X]]] = {
    val m = SkolemFunction2[FM, F, X](f, x)
    Axiom(Fnc(f) ->: IsSet(x) ->: IsSet(v) ->: ((OrderedPair(v, u) in f) /\ (v in x)) ->: (u in m))
  }

  /** `({} in N) /\ ((u in N) ->: ((u union {u}) in N))` */
  def axiomI[U <: AnySet](u: U): Theorem[Member[EmptySet, Infinity] /\ (Member[U, Infinity] ->: Member[Union[U, SingletonSet[U]], Infinity])] =
    Axiom((EmptySet in Infinity) /\ ((u in Infinity) ->: ((u union SingletonSet(u)) in Infinity)))

  /** `M(N)` */
  def axiomIS: Theorem[IsSet[Infinity]] = Axiom(IsSet(Infinity))

  // Definitions

  /** `x union y = -(-x inter -y)` */
  def unionIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Union[X, Y] === -[Intersect[-[X], -[Y]]]] =
    Axiom((x union y) === -(-x inter -y))

  /** `{x} = {x, x}` */
  def singletonEq[X <: AnySet](x: X): Theorem[SingletonSet[X] === PairSet[X, X]] =
    Axiom(SingletonSet(x) === PairSet(x, x))

  /** `<x, y> = {{x}, {x, y}}` */
  def orderedPairEq[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[OrderedPair[X, Y] === PairSet[SingletonSet[X], PairSet[X, Y]]] =
    Axiom(OrderedPair(x, y) === PairSet(SingletonSet(x), PairSet(x, y)))

  /** `U = -{}` */
  def universeIff: Theorem[Universe === -[EmptySet]] = Axiom(Universe === -EmptySet)

  /** `x diff y = x inter -y` */
  def differenceIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Difference[X, Y] === Intersect[X, -[Y]]] =
    Axiom((x diff y) === (x inter -y))

  type FP1 = "p1"
  def isSetP1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[SkolemFunction3[FP1, X, Y, Z]]] = Axiom(IsSet(SkolemFunction3[FP1, X, Y, Z](x, y, z)))
  type FP2 = "p2"
  def isSetP2[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[SkolemFunction3[FP2, X, Y, Z]]] = Axiom(IsSet(SkolemFunction3[FP2, X, Y, Z](x, y, z)))

  /** `M(z) -> (z in (x * y)) -> ((z = <fp1, fp2>) /\ (fp1 in x) /\ (fp2 in y))` */
  def productIff1[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z):
  Theorem[IsSet[Z] ->: Member[Z, Product[X, Y]] ->: ((Z === OrderedPair[SkolemFunction3[FP1, X, Y, Z], SkolemFunction3[FP2, X, Y, Z]]) /\ Member[SkolemFunction3[FP1, X, Y, Z], X] /\ Member[SkolemFunction3[FP2, X, Y, Z], Y])] = {
    val (u, v) = (SkolemFunction3[FP1, X, Y, Z](x, y, z), SkolemFunction3[FP2, X, Y, Z](x, y, z))
    Axiom(IsSet(z) ->: (z in Product(x, y)) ->: ((z === OrderedPair(u, v)) /\ (u in x) /\ (v in y)))
  }

  /** `M(u) -> M(v) -> M(z) -> ((z = <u, v>) /\ (u in x) /\ (v in y)) -> (z in (x * y)))` */
  def productIff2[X <: AnySet, Y <: AnySet, Z <: AnySet, U <: AnySet, V <: AnySet](x: X, y: Y, z: Z, u: U, v: V):
  Theorem[IsSet[U] ->: IsSet[V] ->: IsSet[Z] ->: ((Z === OrderedPair[U, V]) /\ Member[U, X] /\ Member[V, Y]) ->: Member[Z, Product[X, Y]]] =
    Axiom(IsSet(u) ->: IsSet(v) ->: IsSet(z) ->: ((z === OrderedPair(u, v)) /\ (u in x) /\ (v in y)) ->: (z in Product(x, y)))

  /** `Rel(x) <-> (x sube U * U)` */
  def relationIff[X <: AnySet](x: X): Theorem[Relation[X] <-> SubsetEqual[X, Product[Universe, Universe]]] =
    Axiom(Relation(x) <-> (x sube Product(Universe, Universe)))

  /** `M(x) -> ((x in P(y)) <-> (x sube y))` */
  def powerIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: (Member[X, Power[Y]] <-> SubsetEqual[X, Y])] =
    Axiom(IsSet(x) ->: ((x in Power(y)) <-> (x sube y)))

  type FQ = "q"
  def isSetQ[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[SkolemFunction2[FQ, X, Y]]] = Axiom(IsSet(SkolemFunction2[FQ, X, Y](x, y)))

  /** `M(z) -> (z in U(x)) -> ((z in q(x, z) /\ (q(x, z) in x))` */
  def sumIff1[X <: AnySet, Z <: AnySet](x: X, z: Z): Theorem[IsSet[Z] ->: Member[Z, Sum[X]] ->: (Member[Z, SkolemFunction2[FQ, X, Z]] /\ Member[SkolemFunction2[FQ, X, Z], X])] = {
    val v = SkolemFunction2[FQ, X, Z](x, z)
    Axiom(IsSet(z) ->: (z in Sum(x)) ->: ((z in v) /\ (v in x)))
  }

  /** `M(y) -> M(z) -> ((z in y) /\ (y in x)) -> (z in U(x))` */
  def sumIff2[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Y] ->: IsSet[Z] ->: (Member[Z, Y] /\ Member[Y, X]) ->: Member[Z, Sum[X]]] =
    Axiom(IsSet(y) ->: IsSet(z) ->: ((z in y) /\ (y in x)) ->: (z in Sum(x)))

  type FF1 = "f1"
  type FF2 = "f2"
  type FF3 = "f3"
  def isSetF1[X <: AnySet](x: X): Theorem[IsSet[SkolemFunction1[FF1, X]]] = Axiom(IsSet(SkolemFunction1[FF1, X](x)))
  def isSetF2[X <: AnySet](x: X): Theorem[IsSet[SkolemFunction1[FF2, X]]] = Axiom(IsSet(SkolemFunction1[FF2, X](x)))
  def isSetF3[X <: AnySet](x: X): Theorem[IsSet[SkolemFunction1[FF3, X]]] = Axiom(IsSet(SkolemFunction1[FF3, X](x)))

  /** `M(u) -> M(v) -> M(w) -> Fnc(x) -> (Rel(x) /\ (((<u, v> in x) /\ (<u, w> in x)) -> (v = w)))` */
  def functionIff1[X <: AnySet, U <: AnySet, V <: AnySet, W <: AnySet](x: X, u: U, v: V, w: W):
  Theorem[IsSet[U] ->: IsSet[V] ->: IsSet[W] ->: Fnc[X] ->: (Relation[X] /\ ((Member[OrderedPair[U, V], X] /\ Member[OrderedPair[U, W], X]) ->: (V === W)))] =
    Axiom(IsSet(u) ->: IsSet(v) ->: IsSet(w) ->: Fnc(x) ->: (Relation(x) /\ (((OrderedPair(u, v) in x) /\ (OrderedPair(u, w) in x)) ->: (v === w))))

  /** `(Rel(x) /\ (((<f1, f2> in x) /\ (<f1, f3> in x)) -> (f2 = f3))) -> Fnc(x)` */
  def functionIff2[X <: AnySet](x: X):
  Theorem[(Relation[X] /\ ((Member[OrderedPair[SkolemFunction1[FF1, X], SkolemFunction1[FF2, X]], X] /\ Member[OrderedPair[SkolemFunction1[FF1, X], SkolemFunction1[FF3, X]], X]) ->: (SkolemFunction1[FF2, X] === SkolemFunction1[FF3, X]))) ->: Fnc[X]] = {
    val f1 = SkolemFunction1[FF1, X](x)
    val f2 = SkolemFunction1[FF2, X](x)
    val f3 = SkolemFunction1[FF3, X](x)
    Axiom((Relation(x) /\ (((OrderedPair(f1, f2) in x) /\ (OrderedPair(f1, f3) in x)) ->: (f2 === f3))) ->: Fnc(x))
  }

  /** `(<x, y> in Inv(z)) <-> (<y, x> in z)` */
  def inverseIff[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Member[OrderedPair[X, Y], Inverse[Z]] <-> Member[OrderedPair[Y, X], Z]] =
    Axiom((OrderedPair(x, y) in Inverse(z)) <-> (OrderedPair(y, x) in z))

  type FR = "r"
  def isSetR[F <: AnySet, Z <: AnySet](f: F, z: Z): Theorem[IsSet[SkolemFunction2[FR, F, Z]]] = Axiom(IsSet(SkolemFunction2[FR, F, Z](f, z)))

  /** `M(z) -> (z in R(f)) -> (<r(f, z), z> in f)` */
  def rangeIff1[F <: AnySet, Z <: AnySet](f: F, z: Z): Theorem[IsSet[Z] ->: Member[Z, Range[F]] ->: Member[OrderedPair[SkolemFunction2[FR, F, Z], Z], F]] =
    Axiom(IsSet(z) ->: (z in Range(f)) ->: (OrderedPair(SkolemFunction2[FR, F, Z](f, z), z) in f))

  type FI = "i"
  def isSetI[X <: AnySet](x: X): Theorem[IsSet[SkolemFunction1[FI, X]]] = Axiom(IsSet(SkolemFunction1[FI, X](x)))

  /** `M(x) -> (x in I) -> (x = <i(x), i(x)>)` */
  def identityIff1[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, Identity] ->: (X === OrderedPair[SkolemFunction1[FI, X], SkolemFunction1[FI, X]])] =
    Axiom(IsSet(x) ->: (x in Identity) ->: (x === OrderedPair(SkolemFunction1[FI, X](x), SkolemFunction1[FI, X](x))))

  /** `M(x) -> M(y) -> (x = <y, y>) -> (x in I)` */
  def identityIff2[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (X === OrderedPair[Y, Y]) ->: Member[X, Identity]] =
    Axiom(IsSet(x) ->: IsSet(y) ->: (x === OrderedPair(y, y)) ->: (x in Identity))

  /** `Russell = D(-mb inter I)` */
  def russellEq: Theorem[Russell === Domain[Intersect[-[MemberRelation], Identity]]] = Axiom(Russell === Domain(-MemberRelation inter Identity))

  /** `M(z) -> (x irr y) <-> (Rel(x) /\ ((z in y) -> ~(<z, z> in x)))` */
  def irreflexiveIff[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Z] ->: (Irreflexive[X, Y] <-> (Relation[X] /\ (Member[Z, Y] ->: ~[Member[OrderedPair[Z, Z], X]])))] =
    Axiom(IsSet(z) ->: ((x irr y) <-> (Relation(x) /\ ((z in y) ->: ~(OrderedPair(z, z) in x)))))

  /** `M(u) -> M(v) -> M(w) -> (x tr y) <-> (Rel(x) /\ (((u in y) /\ (v in y) /\ (w in y) /\ (<u, v> in x) /\ (<v, w> in x)) -> (<u, w> in x)))` */
  def transitiveIff[X <: AnySet, Y <: AnySet, U <: AnySet, V <: AnySet, W <: AnySet](x: X, y: Y, u: U, v: V, w: W):
  Theorem[IsSet[U] ->: IsSet[V] ->: IsSet[W] ->: (Transitive[X, Y] <-> (Relation[X] /\ ((Member[U, Y] /\ Member[V, Y] /\ Member[W, Y] /\ Member[OrderedPair[U, V], X] /\ Member[OrderedPair[V, W], X]) ->: Member[OrderedPair[U, W], X])))] =
    Axiom(IsSet(u) ->: IsSet(v) ->: IsSet(w) ->: ((x tr y) <-> (Relation(x) /\ (((u in y) /\ (v in y) /\ (w in y) /\ (OrderedPair(u, v) in x) /\ (OrderedPair(v, w) in x)) ->: (OrderedPair(u, w) in x)))))

  /** `(x part y) <-> ((x irr y) /\ (x tr y))` */
  def partialIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[PartialOrder[X, Y] <-> (Irreflexive[X, Y] /\ Transitive[X, Y])] =
    Axiom((x part y) <-> ((x irr y) /\ (x tr y)))

  /** `M(u) -> M(v) -> (x con y) <-> (Rel(x) /\ (((u in y) /\ (v in y) /\ ~(u = v)) -> ((<u, v> in x) \/ (<v, u> in x))))` */
  def connectedIff[X <: AnySet, Y <: AnySet, U <: AnySet, V <: AnySet](x: X, y: Y, u: U, v: V):
  Theorem[IsSet[U] ->: IsSet[V] ->: (Connected[X, Y] <-> (Relation[X] /\ ((Member[U, Y] /\ Member[V, Y] /\ ~[U === V]) ->: (Member[OrderedPair[U, V], X] \/ Member[OrderedPair[V, U], X]))))] =
    Axiom(IsSet(u) ->: IsSet(v) ->: ((x con y) <-> (Relation(x) /\ (((u in y) /\ (v in y) /\ ~(u === v)) ->: ((OrderedPair(u, v) in x) \/ (OrderedPair(v, u) in x))))))

  /** `(x tot y) <-> ((x irr y) /\ (x tr y) /\ (x con y))` */
  def totalIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[TotalOrder[X, Y] <-> (Irreflexive[X, Y] /\ Transitive[X, Y] /\ Connected[X, Y])] =
    Axiom((x tot y) <-> ((x irr y) /\ (x tr y) /\ (x con y)))


}
