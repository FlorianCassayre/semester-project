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

  /** `x = y <-> y = x` */
  def equalsSymmetricIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (Y === X)] =
    impliesToIffRule(hypothesis(x === y)(equalsSymmetric), hypothesis(y === x)(equalsSymmetric))

  /** `M(Y)` given `(M(Z) /\ (Z = Y))` */
  def equalsIsSet[Y <: AnySet, Z <: AnySet](thm: Theorem[IsSet[Z] /\ (Z === Y)]): Theorem[IsSet[Y]] = thm.formula match {
    case IsSet(z1) /\ (z2 === y) if z1 == z2 =>
      val f = SkolemFunction1[FC, Z](z1)
      isSetIff2(y, f)(axiomT(z1, y, f)(andExtractLeft(andCommutative(thm)))(isSetIff1(z1)(andExtractLeft(thm))))
  }

  /** M(x) -> M(y) -> ({x, y} = {y, x}) */
  def pairCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (PairSet[X, Y] === PairSet[Y, X])] = {
    type F = SkolemFunction2[FA, PairSet[X, Y], PairSet[Y, X]]
    val (xy, yx) = (PairSet(x, y), PairSet(y, x))
    val z: F = SkolemFunction2(xy, yx)

    hypothesis(IsSet(z))(sz => hypothesis(IsSet(x))(sx => hypothesis(IsSet(y)) { sy =>
      def implies[A <: AnySet, B <: AnySet](ta: Theorem[IsSet[A]], tb: Theorem[IsSet[B]]): Theorem[Member[F, PairSet[A, B]] ->: Member[F, PairSet[B, A]]] = {
        val (a, b) = (ta.formula.s, tb.formula.s)
        val (iff1, iff2) = (axiomP(a, b, z)(ta)(tb)(sz), axiomP(b, a, z)(tb)(ta)(sz))
        impliesTransitive(
          impliesTransitive(
            toImplies(iff1),
            hypothesis((z === a) \/ (z === b))(orCommutative)
          ),
          toImplies(iffCommutative(iff2))
        )
      }

      equalsIff2(xy, yx)(impliesToIffRule(implies(sx, sy), implies(sy, sx)))
    }))(isSetFa(xy, yx))
  }

  /** `M(x) -> M(y) -> ((x in {y}) <-> (x = y))` */
  def singletonEquals[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> (X === Y))] =
    hypothesis(IsSet(x))(sx => hypothesis(IsSet(y)) { sy =>
      iffTransitive(
        equalsIff1(SingletonSet(y), PairSet(y, y), x)(singletonIff(y)),
        iffTransitive(axiomP(y, y, x)(sy)(sy)(sx), impliesToIffRule(hypothesis((x === y) \/ (x === y))(orUnduplicate), hypothesis(x === y)(orDuplicate)))
      )
    })

  /** `M(x) -> M(y) -> ((x in {y}) <-> (y in {x}))` */
  def singletonMembershipCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> Member[Y, SingletonSet[X]])] =
    hypothesis(IsSet(x))(sx => hypothesis(IsSet(y)) { sy =>
      iffTransitive(iffTransitive(singletonEquals(x, y)(sx)(sy), equalsSymmetricIff(x, y)), iffCommutative(singletonEquals(y, x)(sy)(sx)))
    })

  /** `M(x) -> M(y) -> ({x} = {y} <-> x = y)` */
  def singletonCongruence[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: ((SingletonSet[X] === SingletonSet[Y]) <-> (X === Y))] = {
    hypothesis(IsSet(x))(sx => hypothesis(IsSet(y)) { sy =>

      val to = hypothesis(SingletonSet(x) === SingletonSet(y)) { xy =>
        iffTransitive(
          iffTransitive(
            iffCommutative(singletonEquals(x, x)(sx)(sx)),
            equalsIff1(SingletonSet(x), SingletonSet(y), x)(xy)
          ),
          singletonEquals(x, y)(sx)(sy)
        )(equalsReflexive(x))
      }

      val from = hypothesis(x === y) { xy =>
        val f = SkolemFunction2[FA, SingletonSet[X], SingletonSet[Y]](SingletonSet(x), SingletonSet(y))
        val setFa = isSetFa(SingletonSet(x), SingletonSet(y))
        equalsIff2(SingletonSet(x), SingletonSet(y))(iffTransitive(
          iffTransitive(
            singletonMembershipCommutative(f, x)(setFa)(sx),
            axiomT(x, y, SingletonSet(f))(xy)
          ),
          singletonMembershipCommutative(y, f)(sy)(setFa)
        ))
      }

      impliesToIffRule(to, from)
    })
  }

  /** `(x inter y) = (y inter x)` */
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
