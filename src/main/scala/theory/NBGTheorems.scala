package theory

trait NBGTheorems extends NBGRules {

  /** `(x = y) <-> ((x sube y) /\ (y sube x))` */
  def equalsSubset[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (SubsetEqual[X, Y] /\ SubsetEqual[Y, X])] = {
    val to = assume(x === y) { xy =>
      andCombine(
        subsetEqIff2(x, y)(toImplies(equalsIff1(x, y, SkolemFunction2[FB, X, Y](x, y))(xy))),
        subsetEqIff2(y, x)(toImplies(equalsIff1(y, x, SkolemFunction2[FB, Y, X](y, x))(equalsSymmetric(xy))))
      )
    }
    val from = assume((x sube y) /\ (y sube x)) { sub =>
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
    impliesToIffRule(assume(x === y)(equalsSymmetric), assume(y === x)(equalsSymmetric))

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
    val sz = isSetFa(xy, yx)

    assume(IsSet(x), IsSet(y)) { (sx, sy) =>
      def implies[A <: AnySet, B <: AnySet](ta: Theorem[IsSet[A]], tb: Theorem[IsSet[B]]): Theorem[Member[F, PairSet[A, B]] ->: Member[F, PairSet[B, A]]] = {
        val (a, b) = (ta.formula.s, tb.formula.s)
        val (iff1, iff2) = (axiomP(a, b, z)(ta)(tb)(sz), axiomP(b, a, z)(tb)(ta)(sz))
        impliesTransitive(
          impliesTransitive(
            toImplies(iff1),
            assume((z === a) \/ (z === b))(orCommutative)
          ),
          toImplies(iffCommutative(iff2))
        )
      }

      equalsIff2(xy, yx)(impliesToIffRule(implies(sx, sy), implies(sy, sx)))
    }
  }

  /** `M(x) -> M(y) -> ((x in {y}) <-> (x = y))` */
  def singletonEquals[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> (X === Y))] =
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>
      iffTransitive(
        equalsIff1(SingletonSet(y), PairSet(y, y), x)(singletonEq(y)),
        iffTransitive(axiomP(y, y, x)(sy)(sy)(sx), impliesToIffRule(assume((x === y) \/ (x === y))(orUnduplicate), assume(x === y)(t => orAddRight(t, t.formula))))
      )
    }

  /** `M(x) -> M(y) -> ((x in {y}) <-> (y in {x}))` */
  def singletonMembershipCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> Member[Y, SingletonSet[X]])] =
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>
      iffTransitive(iffTransitive(singletonEquals(x, y)(sx)(sy), equalsSymmetricIff(x, y)), iffCommutative(singletonEquals(y, x)(sy)(sx)))
    }

  /** `M(x) -> M(y) -> ({x} = {y} <-> x = y)` */
  def singletonCongruence[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: ((SingletonSet[X] === SingletonSet[Y]) <-> (X === Y))] = {
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>

      val to = assume(SingletonSet(x) === SingletonSet(y)) { xy =>
        iffTransitive(
          iffTransitive(
            iffCommutative(singletonEquals(x, x)(sx)(sx)),
            equalsIff1(SingletonSet(x), SingletonSet(y), x)(xy)
          ),
          singletonEquals(x, y)(sx)(sy)
        )(equalsReflexive(x))
      }

      val from = assume(x === y) { xy =>
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
    }
  }

  /** `M({x, y})` given `M(x)` and `M(y)` */
  def pairIsSet[X <: AnySet, Y <: AnySet](tx: Theorem[IsSet[X]], ty: Theorem[IsSet[Y]]): Theorem[IsSet[PairSet[X, Y]]] = {
    val (x, y) = (tx.formula.s, ty.formula.s)
    axiomPS(x, y)(tx)(ty)
  }

  /** `M({x})` given `M(x)` */
  def singletonIsSet[X <: AnySet](thm: Theorem[IsSet[X]]): Theorem[IsSet[SingletonSet[X]]] = thm.formula match {
    case IsSet(x) => equalsIsSet(andCombine(pairIsSet(thm, thm), equalsSymmetric(singletonEq(x))))
  }

  /** `M(x) -> M(y) -> M(z) -> {z} = {x, y} -> z = x` */
  def singletonPairEqualLeft[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z):
  Theorem[IsSet[X] ->: IsSet[Y] ->: IsSet[Z] ->: (SingletonSet[Z] === PairSet[X, Y]) ->: (Z === X)] =
    assume(IsSet(x), IsSet(y), IsSet(z), SingletonSet(z) === PairSet(x, y)) { (sx, sy, sz, hyp) =>
      equalsSymmetric(iffTransitive(
        iffCommutative(axiomP(x, y, x)(sx)(sy)(sx)),
        iffTransitive(
          iffCommutative(equalsIff1(SingletonSet(z), PairSet(x, y), x)(hyp)),
          singletonEquals(x, z)(sx)(sz)
        )
      )(orAddRight(equalsReflexive(x), x === y)))
    }

  /** `M(x) -> M(y) -> M(u) -> M(v) -> <x, y> = <u, v> -> (x = u /\ y = v)` */
  def orderedPairToEquals[X <: AnySet, Y <: AnySet, U <: AnySet, V <: AnySet](x: X, y: Y, u: U, v: V):
  Theorem[IsSet[X] ->: IsSet[Y] ->: IsSet[U] ->: IsSet[V] ->: (OrderedPair[X, Y] === OrderedPair[U, V]) ->: ((X === U) /\ (Y === V))] = {
    assume(IsSet(x), IsSet(y), IsSet(u), IsSet(v), OrderedPair(x, y) === OrderedPair(u, v)) { (sx, sy, su, sv, xyuv) =>
      val (ssx, ssu, suv, sxy) = (singletonIsSet(sx), singletonIsSet(su), pairIsSet(su, sv), pairIsSet(sx, sy))
      val (sX, sU) = (SingletonSet(x), SingletonSet(u))
      val (pXY, pUV) = (PairSet(x, y), PairSet(u, v))

      val assumption = equalsTransitive(equalsTransitive(equalsSymmetric(orderedPairEq(x, y)), xyuv), orderedPairEq(u, v))

      // Left conclusion
      val xEu: Theorem[X === U] = orCase(
        axiomP(sU, pUV, sX)(ssu)(suv)(ssx)(
          equalsIff1(PairSet(sX, pXY), PairSet(sU, pUV), sX)(assumption)(
            iffCommutative(axiomP(sX, pXY, sX)(ssx)(sxy)(ssx))(
              orAddRight(equalsReflexive(sX), sX === pXY)
            )
          )
        ),
        assume(sX === sU)(singletonCongruence(x, u)(sx)(su).apply),
        singletonPairEqualLeft(u, v, x)(su)(sv)(sx)
      )

      // Right conclusion
      val yEv: Theorem[Y === V] = mixedDoubleNegationInvert(assume(~(y === v)) { yv =>
        val or = assume(~(x === v) \/ ~(y === u)) { hyp =>
          val xv: Theorem[(~[X === V]) ->: False] = assume(~(x === v)) { hyp =>
            val lemma = impliesTransitive(impliesInverse(assume(pUV === sX)(hyp =>
              singletonPairEqualLeft(v, u, x)(sv)(su)(sx)(equalsTransitive(equalsSymmetric(hyp), pairCommutative(u, v)(su)(sv)))
            )), orImplies(axiomP(sX, pXY, pUV)(ssx)(sxy)(suv)(
              equalsIff1(PairSet(sU, pUV), PairSet(sX, pXY), pUV)(
                equalsSymmetric(assumption))(iffCommutative(axiomP(sU, pUV, pUV)(ssu)(suv)(suv))(
                orCommutative(orAddRight(equalsReflexive(pUV), pUV === sU))
              ))))
            )

            val vxOvy = axiomP(x, y, v)(sx)(sy)(sv)(
              equalsIff1(pUV, pXY, v)(mixedDoubleNegationInvert(lemma(hyp)))(
                iffCommutative(axiomP(u, v, v)(su)(sv)(sv))(orCommutative(orAddRight(equalsReflexive(v), v === u)))
              )
            )
            mixedDoubleNegation(equalsSymmetric(mixedDoubleNegationInvert(orImplies(vxOvy)(
              iffCommutative(notIff(v === x))(impliesTransitive(assume(v === x)(equalsSymmetric), notIff(x === v)(hyp)))
            ))))(yv)
          }

          val yu: Theorem[~[Y === U] ->: False] = assume(~(y === u)) { hyp =>
            val lemma = impliesTransitive(
              impliesInverse(assume(pXY === sU)(hyp =>
                equalsSymmetric(singletonPairEqualLeft(y, x, u)(sy)(sx)(su)(equalsTransitive(equalsSymmetric(hyp), pairCommutative(x, y)(sx)(sy))))
              )), orImplies(axiomP(sU, pUV, pXY)(ssu)(suv)(sxy)(
                equalsIff1(PairSet(sX, pXY), PairSet(sU, pUV), pXY)(assumption)(
                  iffCommutative(axiomP(sX, pXY, pXY)(ssx)(sxy)(sxy))(
                    orCommutative(orAddRight(equalsReflexive(pXY), pXY === sX))
                  )
                )
              )))
            val yuOyv = axiomP(u, v, y)(su)(sv)(sy)(
              iffCommutative(equalsIff1(pUV, pXY, y)(equalsSymmetric(mixedDoubleNegationInvert(lemma(hyp)))))(
                iffCommutative(axiomP(x, y, y)(sx)(sy)(sy))(orCommutative(orAddRight(equalsReflexive(y), y === x)))
              )
            )
            notIff(y === v)(yv)(mixedDoubleNegationInvert(orImplies(yuOyv)(hyp)))
          }

          orCase(hyp, xv, yu)
        }

        notIff(y === v)(yv)(
          equalsTransitive(
            equalsTransitive(
              notUnduplicate(andExtractLeft(andCommutative(
                notUnduplicate(impliesInverse(toImplies(iffCommutative(orIff(~(x === v), ~(y === u)))))(
                  iffCommutative(notIff(~(x === v) \/ ~(y === u)))(or)
                ))
              ))),
              equalsSymmetric(xEu)), notUnduplicate(andExtractLeft(
              notUnduplicate(impliesInverse(toImplies(iffCommutative(orIff(~(x === v), ~(y === u)))))(
                iffCommutative(notIff(~(x === v) \/ ~(y === u)))(or)
              ))
            ))
          )
        )
      })

      andCombine(xEu, yEv)
    }
  }

  /** `(x inter y) = (y inter x)` */
  def intersectCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Intersect[X, Y] === Intersect[Y, X]] = {
    type C = SkolemFunction2[FA, Intersect[X, Y], Intersect[Y, X]]

    def schema[A <: AnySet, B <: AnySet](a: A, b: B): Theorem[Member[C, Intersect[A, B]] ->: Member[C, Intersect[B, A]]] = {
      val c: C = SkolemFunction2(x inter y, y inter x)
      impliesTransitive(
        impliesTransitive(toImplies(intersectIff(a, b, c)), assume((c in a) /\ (c in b))(andCommutative)),
        toImplies(iffCommutative(intersectIff(b, a, c)))
      )
    }

    equalsIff2(x inter y, y inter x)(impliesToIffRule(schema(x, y), schema(y, x)))
  }

}
