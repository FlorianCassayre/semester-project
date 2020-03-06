package theory

trait NBGTheorems extends NBGRules {

  /** `(x = y) <-> ((x sube y) /\ (y sube x))` */
  def equalsSubset[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (SubsetEqual[X, Y] /\ SubsetEqual[Y, X])] = {
    val to = hypothesis(x === y) { xy =>
      andCombine(
        subsetEqIff2(x, y)(toImplies(equalsIff1(x, y, SkolemFunction2[FB, X, Y](x, y))(xy))),
        subsetEqIff2(y, x)(toImplies(equalsIff1(y, x, SkolemFunction2[FB, Y, X](y, x))(equalsSymmetric(xy))))
      )
    }
    val from = hypothesis((x sube y) /\ (y sube x)) { sub =>
      val z = SkolemFunction2[FA, X, Y](x, y)
      val (lhs, rhs) = (subsetEqIff1(x, y, z)(andExtractLeft(sub)), subsetEqIff1(y, x, z)(andExtractLeft(andCommutative(sub))))
      equalsIff2(x, y) {
        val and = andCombine(lhs, rhs)
        impliesToIff(z in x, z in y)(andExtractLeft(and))(andExtractLeft(andCommutative(and)))
      }
    }

    impliesToIff(x === y, (x sube y) /\ (y sube x))(to)(from)
  }

  /** `x = x` */
  def equalsReflexive[X <: AnySet](x: X): Theorem[X === X] =
    equalsIff2(x, x)(iffReflexive(SkolemFunction2[FA, X, X](x, x) in x))

  /** `y = x` given `x = y` */
  def equalsSymmetric[X <: AnySet, Y <: AnySet](thm: Theorem[X === Y]): Theorem[Y === X] = thm.formula match {
    case x === y =>
      equalsIff2(y, x)(iffCommutative(equalsIff1(x, y, SkolemFunction2[FA, Y, X](y, x))(thm)))
  }

  /** `x = z` given `x = y` and `y = z` */
  def equalsTransitive[X <: AnySet, Y <: AnySet, Z <: AnySet](xy: Theorem[X === Y], yz: Theorem[Y === Z]): Theorem[X === Z] = (xy.formula, yz.formula) match {
    case (x === y1, y2 === z) if y1 == y2 =>
      val f = SkolemFunction2[FA, X, Z](x, z)
      val and = andCombine(equalsIff1(x, y1, f)(xy), equalsIff1(y1, z, f)(yz))

      equalsIff2(x, z)(iffTransitive(andExtractLeft(and), andExtractLeft(andCommutative(and))))
  }

  /** `M(Y)` given `(M(Z) /\ (Z = Y))` */
  def equalsIsSet[Y <: AnySet, Z <: AnySet](thm: Theorem[IsSet[Z] /\ (Z === Y)]): Theorem[IsSet[Y]] = thm.formula match {
    case IsSet(z1) /\ (z2 === y) if z1 == z2 =>
      val f = SkolemFunction1[FC, Z](z1)
      isSetIff2(y, f)(axiomT(z1, y, f)(andExtractLeft(andCommutative(thm)))(isSetIff1(z1)(andExtractLeft(thm))))
  }



  /** (x inter y) = (y inter x) */
  def intersectCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Intersect[X, Y] === Intersect[Y, X]] = {
    type C = SkolemFunction2[FA, Intersect[X, Y], Intersect[Y, X]]

    def schema[A <: AnySet, B <: AnySet](a: A, b: B): Theorem[Member[C, Intersect[A, B]] ->: Member[C, Intersect[B, A]]] = {
      val c: C = SkolemFunction2(x inter y, y inter x)
      impliesTransitive(
        impliesTransitive(toImplies(intersectIff(a, b, c)), hypothesis((c in a) /\ (c in b))(andCommutative)),
        toImplies(iffCommutative(intersectIff(b, a, c)))
      )
    }

    equalsIff2(x inter y, y inter x)(impliesToIffRule(schema(x, y), schema(y, x)))
  }

}
