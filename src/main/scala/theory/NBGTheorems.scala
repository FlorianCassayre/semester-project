package theory

trait NBGTheorems extends NBGRules {

  type ZEq[X <: AnySet, Y <: AnySet] = SkolemFunction2[FA, X, Y]

  private def zEq[X <: AnySet, Y <: AnySet](x: X, y: Y): ZEq[X, Y] = SkolemFunction2[FA, X, Y](x, y)

  private def zEqPair[X <: AnySet, Y <: AnySet](x: X, y: Y): (ZEq[X, Y], Theorem[IsSet[SkolemFunction2[FA, X, Y]]]) =
    (SkolemFunction2[FA, X, Y](x, y), isSetFa(x, y))

  /** `(x = y) <-> ((x sube y) /\ (y sube x))` */
  def equalsSubset[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (SubsetEqual[X, Y] /\ SubsetEqual[Y, X])] = {
    val ~> = assume(x === y) { xy =>
      andCombine(
        subsetEqIff2(x, y)(toImplies(equalsIff1(x, y, SkolemFunction2[FB, X, Y](x, y))(xy))),
        subsetEqIff2(y, x)(toImplies(equalsIff1(y, x, SkolemFunction2[FB, Y, X](y, x))(equalsSymmetric(xy))))
      )
    }
    val <~ = assume((x sube y) /\ (y sube x)) { sub =>
      val z = zEq(x, y)
      val (lhs, rhs) = (subsetEqIff1(x, y, z)(andExtractLeft(sub)), subsetEqIff1(y, x, z)(andExtractLeft(andCommutative(sub))))
      equalsIff2(x, y) {
        val and = andCombine(lhs, rhs)
        impliesToIff(z in x, z in y)(andExtractLeft(and))(andExtractLeft(andCommutative(and)))
      }
    }

    impliesToIffRule(~>, <~)
  }

  /** `x = x` */
  def equalsReflexive[X <: AnySet](x: X): Theorem[X === X] =
    equalsIff2(x, x)(iffReflexive(zEq(x, x) in x))

  /** `y = x` given `x = y` */
  def equalsSymmetric[X <: AnySet, Y <: AnySet](thm: Theorem[X === Y]): Theorem[Y === X] = thm.formula match {
    case x === y =>
      equalsIff2(y, x)(iffCommutative(equalsIff1(x, y, zEq(y, x))(thm)))
  }

  /** `x = z` given `x = y` and `y = z` */
  def equalsTransitive[X <: AnySet, Y <: AnySet, Z <: AnySet](xy: Theorem[X === Y], yz: Theorem[Y === Z]): Theorem[X === Z] = (xy.formula, yz.formula) match {
    case (x === y1, y2 === z) if y1 == y2 =>
      val f = zEq(x, z)
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
    type F = ZEq[PairSet[X, Y], PairSet[Y, X]]
    val (xy, yx) = (PairSet(x, y), PairSet(y, x))
    val (z, sz) = zEqPair(xy, yx)

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

      val ~> = assume(SingletonSet(x) === SingletonSet(y)) { xy =>
        iffTransitive(
          iffTransitive(
            iffCommutative(singletonEquals(x, x)(sx)(sx)),
            equalsIff1(SingletonSet(x), SingletonSet(y), x)(xy)
          ),
          singletonEquals(x, y)(sx)(sy)
        )(equalsReflexive(x))
      }

      val <~ = assume(x === y) { xy =>
        val (f, setFa) = zEqPair(SingletonSet(x), SingletonSet(y))
        equalsIff2(SingletonSet(x), SingletonSet(y))(iffTransitive(
          iffTransitive(
            singletonMembershipCommutative(f, x)(setFa)(sx),
            axiomT(x, y, SingletonSet(f))(xy)
          ),
          singletonMembershipCommutative(y, f)(sy)(setFa)
        ))
      }

      impliesToIffRule(~>, <~)
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

  /** `M(z) -> (z in (x union y) <-> ((z in x) \/ (z in y)))` */
  def unionContains[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Z] ->: (Member[Z, Union[X, Y]] <-> (Member[Z, X] \/ Member[Z, Y]))] = assume(IsSet(z)) { sz =>
    val ~> = assume(z in (x union y)) { hyp =>
      notUnduplicate(impliesInverse(
        assume(~((z in x) \/ (z in y)))(hyp2 =>
          andCombine(
            iffCommutative(complementIff(x, z)(sz))(andExtractLeft(iffSwapNot(orIff(z in x, z in y))(hyp2))),
            iffCommutative(complementIff(y, z)(sz))(andExtractLeft(andCommutative(iffSwapNot(orIff(z in x, z in y))(hyp2))))
          )
        )
      )(
        iffAddNot(intersectIff(-x, -y, z)(sz))(complementIff(-x inter -y, z)(sz)(equalsIff1(x union y, -(-x inter -y), z)(unionIff(x, y))(hyp)))
      ))
    }

    val <~ = assume((z in x) \/ (z in y)) { hyp =>
      equalsIff1(-(-x inter -y), x union y, z)(equalsSymmetric(unionIff(x, y)))(iffCommutative(complementIff(-x inter -y, z)(sz))(
        iffCommutative(notIff(z in (-x inter -y)))(impliesTransitive(
          impliesTransitive(
            toImplies(intersectIff(-x, -y, z)(sz)),
            assume((z in -x) /\ (z in -y))(hyp2 =>
              andCombine(complementIff(x, z)(sz)(andExtractLeft(hyp2)), complementIff(y, z)(sz)(andExtractLeft(andCommutative(hyp2))))
            )
          ),
          notIff(~(z in x) /\ ~(z in y))(orIff(z in x, z in y)(hyp))
        ))
      ))
    }

    impliesToIffRule(~>, <~)
  }

  /** `M(x) -> (x in U)` */
  def universeContains[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, Universe]] =
    assume(IsSet(x))(sx => iffCommutative(iffTransitive(equalsIff1(Universe, -EmptySet, x)(universeIff), complementIff(EmptySet, x)(sx)))(axiomN(x)(sx)))

  /** `M(z) -> (z in (x diff y) <-> ((z in x) /\ ~(z in y)))` */
  def differenceContains[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[IsSet[Z] ->: (Member[Z, Difference[X, Y]] <-> (Member[Z, X] /\ ~[Member[Z, Y]]))] = assume(IsSet(z)) { sz =>
    val ~> = assume(z in (x diff y)) { hyp =>
      val t = intersectIff(x, -y, z)(sz)(equalsIff1(x diff y, x inter -y, z)(differenceIff(x, y))(hyp))
      andCombine(andExtractLeft(t), complementIff(y, z)(sz)(andExtractLeft(andCommutative(t))))
    }

    val <~ = assume((z in x) /\ ~(z in y)) { hyp =>
      equalsIff1(x inter -y, x diff y, z)(equalsSymmetric(differenceIff(x, y)))(iffCommutative(intersectIff(x, -y, z)(sz))(
        andCombine(andExtractLeft(hyp), iffCommutative(complementIff(y, z)(sz))(andExtractLeft(andCommutative(hyp))))
      ))
    }

    impliesToIffRule(~>, <~)
  }

  /** `(x inter y) = (y inter x)` */
  def intersectCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Intersect[X, Y] === Intersect[Y, X]] = {
    type C = ZEq[Intersect[X, Y], Intersect[Y, X]]
    val (xy, yx) = (x inter y, y inter x)
    val (c, sc) = zEqPair(xy, yx)

    def schema[A <: AnySet, B <: AnySet](a: A, b: B): Theorem[Member[C, Intersect[A, B]] ->: Member[C, Intersect[B, A]]] =
      impliesTransitive(
        impliesTransitive(toImplies(intersectIff(a, b, c)(sc)), assume((c in a) /\ (c in b))(andCommutative)),
        toImplies(iffCommutative(intersectIff(b, a, c)(sc)))
      )

    equalsIff2(xy, yx)(impliesToIffRule(schema(x, y), schema(y, x)))
  }

  /** `x = y <-> -x = -y` */
  def complementCongruence[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (-[X] === -[Y])] = {
    val ~> = assume(x === y) { hyp =>
      val (z, sz) = zEqPair(-x, -y)

      equalsIff2(-x, -y)(iffTransitive(
        iffTransitive(
          complementIff(x, z)(sz),
          iffAddNot(equalsIff1(x, y, z)(hyp))
        ),
        iffCommutative(complementIff(y, z)(sz))
      ))
    }

    val <~ = assume(-x === -y) { hyp =>
      val (z, sz) = zEqPair(x, y)

      equalsIff2(x, y)(iffRemoveNot(iffTransitive(
        iffTransitive(
          iffCommutative(complementIff(x, z)(sz)),
          equalsIff1(-x, -y, z)(hyp)
        ),
        complementIff(y, z)(sz)
      )))
    }

    impliesToIffRule(~>, <~)
  }

  /** `(x union y) = (y union x)` */
  def unionCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Union[X, Y] === Union[Y, X]] =
    equalsTransitive(
      equalsTransitive(
        unionIff(x, y),
        complementCongruence(-x inter -y, -y inter -x)(intersectCommutative(-x, -y))
      ),
      equalsSymmetric(unionIff(y, x))
    )

  /** `x sube y <-> (x inter y = x)` */
  def subsetIntersect[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[X, Y] <-> (Intersect[X, Y] === X)] = {
    val ~> : Theorem[SubsetEqual[X, Y] ->: (Intersect[X, Y] === X)] = assume(SubsetEqual(x, y)) { hyp =>
      val z = zEq(x inter y, x)

      equalsIff2(x inter y, x)(iffTransitive(
        intersectIff(x, y, z)(isSetFa(x inter y, x)),
        impliesToIffRule(assume((z in x) /\ (z in y))(andExtractLeft), assume(z in x)(hyp2 => andCombine(hyp2, subsetEqIff1(x, y, z)(hyp)(hyp2))))
      ))
    }

    val <~ : Theorem[(Intersect[X, Y] === X) ->: SubsetEqual[X, Y]] = assume((x inter y) === x) { hyp =>
      val z = SkolemFunction2[FB, X, Y](x, y)

      subsetEqIff2(x, y)(assume(z in x)(hyp2 => andExtractLeft(andCommutative(iffTransitive(
        iffCommutative(equalsIff1(x inter y, x, z)(hyp)),
        intersectIff(x, y, z)(isSetFb(x, y))
      )(hyp2)))))
    }

    impliesToIffRule(~>, <~)
  }

  /** `x sube y <-> (x union y = y)` */
  def subsetUnion[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[X, Y] <-> (Union[X, Y] === Y)] = ???

  /** `(x inter y) inter z = x inter (y inter z)` */
  def intersectAssociative[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Intersect[Intersect[X, Y], Z] === Intersect[X, Intersect[Y, Z]]] = ???

  /** `(x union y) union z = x union (y union z)` */
  def unionAssociative[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Union[Union[X, Y], Z] === Union[X, Union[Y, Z]]] = ???

  /** `(x inter x) = x` */
  def intersectIndempotent[X <: AnySet](x: X): Theorem[Intersect[X, X] === X] = {
    val (z, sz) = zEqPair(x inter x, x)

    val t = intersectIff(x, x, z)(sz)
    val ~> = assume(z in (x inter x))(hyp => andExtractLeft(t(hyp)))
    val <~ = assume(z in x)(hyp => iffCommutative(t)(andCombine(hyp, hyp)))

    equalsIff2(x inter x, x)(impliesToIffRule(~>, <~))
  }

  /** `(x union x) = x` */
  def unionIndempotent[X <: AnySet](x: X): Theorem[Union[X, X] === X] = {
    val (z, sz) = zEqPair(x union x, x)

    val t = unionContains(x, x, z)(sz)
    val ~> = assume(z in (x union x))(hyp => orUnduplicate(t(hyp)))
    val <~ = assume(z in x)(hyp => iffCommutative(t)(orAddRight(hyp, hyp.formula)))

    equalsIff2(x union x, x)(impliesToIffRule(~>, <~))
  }

  /** `(x inter {}) = {}` */
  def intersectEmpty[X <: AnySet](x: X): Theorem[Intersect[X, EmptySet] === EmptySet] = {
    val (z, sz) = zEqPair(x inter EmptySet, EmptySet)

    val t = notIff(z in EmptySet)(axiomN(z)(sz))
    val ~> = assume((z in x) /\ (z in EmptySet))(hyp => exFalso(z in EmptySet)(t(andExtractLeft(andCommutative(hyp)))))
    val <~ = assume(z in EmptySet)(hyp => andCombine(exFalso(z in x)(t(hyp)), hyp))

    equalsIff2(x inter EmptySet, EmptySet)(iffTransitive(intersectIff(x, EmptySet, z)(sz), impliesToIffRule(~>, <~)))
  }

  /** `(x union {}) = x` */
  def unionEmpty[X <: AnySet](x: X): Theorem[Union[X, EmptySet] === X] = ???

  /** `(x inter U) = x` */
  def intersectUniverse[X <: AnySet](x: X): Theorem[Intersect[X, Universe] === X] = ???

  /** `(x union U) = U` */
  def unionUniverse[X <: AnySet](x: X): Theorem[Union[X, Universe] === Universe] = ???

  /** `-(x union y) = (-x union -y)` */
  def unionComplement[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[-[Union[X, Y]] === Union[-[X], -[Y]]] = ???

  /** `-(x inter y) = (-x union -y)` */
  def intersectComplement[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[-[Intersect[X, Y]] === Union[-[X], -[Y]]] = ???

  /** `(x diff x) = {}` */
  def differenceSelf[X <: AnySet](x: X): Theorem[Difference[X, X] === EmptySet] = ???

  /** `(U diff x) = -x` */
  def universeDifference[X <: AnySet](x: X): Theorem[Difference[Universe, X] === -[X]] = ???

  /** `x diff (x diff y) = (x inter y)` */
  def doubleDifference[X <: AnySet, Y <: AnySet]: Theorem[Difference[X, Difference[X, Y]] === Intersect[X, Y]] = ???

  /** `y sube -x -> (x diff y) = x` */
  def subsetDifference[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[Y, -[X]] ->: (Difference[X, Y] === X)] = ???

  /** `--x = x` */
  def doubleComplement[X <: AnySet](x: X): Theorem[-[-[X]] === X] = {
    val (z, sz) = zEqPair(-(-x), x)

    equalsIff2(-(-x), x)(iffTransitive(iffTransitive(complementIff(-x, z)(sz), iffAddNot(complementIff(x, z)(sz))), doubleNotIff(z in x)))
  }

  /** `-U = {}` */
  def universeComplement: Theorem[-[Universe] === EmptySet] = {
    val (z, sz) = zEqPair(-Universe, EmptySet)

    equalsIff2(-Universe, EmptySet)(iffTransitive(complementIff(Universe, z)(sz), iffSwapNot(andToIff(andCombine(universeContains(z)(sz), axiomN(z)(sz))))))
  }

  /** `x inter (y union z) = (x inter y) union (x inter z)` */
  def intersectDistributivity[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Intersect[X, Intersect[Y, Z]] === Union[Intersect[X, Y], Intersect[X, Z]]] = ???

  /** `x union (y inter z) = (x union y) inter (x union z)` */
  def unionDistributivity[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Union[X, Union[Y, Z]] === Intersect[Union[X, Y], Union[X, Z]]] = ???

}
