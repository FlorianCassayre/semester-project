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
        subsetEqIff2(x, y)(equalsIff1(x, y, SkolemFunction2[FB, X, Y](x, y))(xy).toImplies),
        subsetEqIff2(y, x)(equalsIff1(y, x, SkolemFunction2[FB, Y, X](y, x))(equalsSymmetric(xy)).toImplies)
      )
    }
    val <~ = assume((x sube y) /\ (y sube x)) { sub =>
      val z = zEq(x, y)
      equalsIff2(x, y)(subsetEqIff1(x, y, z)(sub.left).combine(subsetEqIff1(y, x, z)(sub.right)))
    }

    ~> combine <~
  }

  /** `x = x` */
  def equalsReflexive[X <: AnySet](x: X): Theorem[X === X] =
    equalsIff2(x, x)((zEq(x, x) in x).reflexive)

  /** `y = x` given `x = y` */
  def equalsSymmetric[X <: AnySet, Y <: AnySet](thm: Theorem[X === Y]): Theorem[Y === X] = thm.formula match {
    case x === y =>
      equalsIff2(y, x)(equalsIff1(x, y, zEq(y, x))(thm).swap)
  }

  /** `x = z` given `x = y` and `y = z` */
  def equalsTransitive[X <: AnySet, Y <: AnySet, Z <: AnySet](xy: Theorem[X === Y], yz: Theorem[Y === Z]): Theorem[X === Z] = (xy.formula, yz.formula) match {
    case (x === y1, y2 === z) if y1 == y2 =>
      val f = zEq(x, z)
      equalsIff2(x, z)(equalsIff1(x, y1, f)(xy).join(equalsIff1(y1, z, f)(yz)))
  }

  /** `x = y <-> y = x` */
  def equalsSymmetricIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (Y === X)] =
    assume(x === y)(equalsSymmetric) combine assume(y === x)(equalsSymmetric)

  /** `(x = y) <-> (a(x, y) in x <-> a(x, y) in y)` */
  def equalsAllIff[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (Member[SkolemFunction2[FA, X, Y], X] <-> Member[SkolemFunction2[FA, X, Y], Y])] = {
    val z = zEq(x, y)
    val ~> = equalsIff1(x, y, z)
    val <~ = equalsIff2(x, y)
    ~> combine <~
  }

  /** `M(Y)` given `(M(Z) /\ (Z = Y))` */
  def equalsIsSet[Y <: AnySet, Z <: AnySet](thm: Theorem[IsSet[Z] /\ (Z === Y)]): Theorem[IsSet[Y]] = thm.formula match {
    case IsSet(z1) /\ (z2 === y) if z1 == z2 =>
      val f = SkolemFunction1[FC, Z](z1)
      isSetIff2(y, f)(axiomT(z1, y, f)(thm.right)(isSetIff1(z1)(thm.left)))
  }

  implicit class WrapperEquals[X <: AnySet, Y <: AnySet](thm: Theorem[X === Y]) {
    private val (x, y) = (thm.a, thm.b)
    def join[Z <: AnySet](that: Theorem[Y === Z]): Theorem[X === Z] = equalsTransitive(thm, that)
    def swap: Theorem[Y === X] = equalsSymmetric(thm)
    def toImplies[Z <: AnySet](z: Z): Theorem[Member[Z, X] <-> Member[Z, Y]] = equalsIff1(x, y, z)(thm)
  }

  implicit class WrapperAnySet[X <: AnySet](x: X) {
    def reflexive: Theorem[X === X] = equalsReflexive(x)
  }

  implicit class WrapperIffEquals[X <: AnySet, Y <: AnySet](thm: Theorem[Member[SkolemFunction2[FA, X, Y], X] <-> Member[SkolemFunction2[FA, X, Y], Y]]) {
    private val (x, y) = thm.formula match {
      case Member(_, x) <-> Member(_, y) => (x, y)
    }
    def toEquals: Theorem[X === Y] = equalsIff2(x, y)(thm)
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

        iff1.toImplies join
          assume((z === a) \/ (z === b))(orCommutative) join
          iff2.swap.toImplies
      }

      equalsIff2(xy, yx)(implies(sx, sy) combine implies(sy, sx))
    }
  }

  /** `M(x) -> M(y) -> ((x in {y}) <-> (x = y))` */
  def singletonEquals[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> (X === Y))] =
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>
        equalsIff1(SingletonSet(y), PairSet(y, y), x)(singletonEq(y)) join
        axiomP(y, y, x)(sy)(sy)(sx) join
          (assume((x === y) \/ (x === y))(orUnduplicate) combine assume(x === y)(t => orAddRight(t, t.formula)))
    }

  /** `M(x) -> M(y) -> ((x in {y}) <-> (y in {x}))` */
  def singletonMembershipCommutative[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: (Member[X, SingletonSet[Y]] <-> Member[Y, SingletonSet[X]])] =
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>
      singletonEquals(x, y)(sx)(sy) join equalsSymmetricIff(x, y) join singletonEquals(y, x)(sy)(sx).swap
    }

  /** `M(x) -> M(y) -> ({x} = {y} <-> x = y)` */
  def singletonCongruence[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[IsSet[X] ->: IsSet[Y] ->: ((SingletonSet[X] === SingletonSet[Y]) <-> (X === Y))] = {
    assume(IsSet(x), IsSet(y)) { (sx, sy) =>

      val ~> = assume(SingletonSet(x) === SingletonSet(y)) { xy =>
        (iffCommutative(singletonEquals(x, x)(sx)(sx)) join
          equalsIff1(SingletonSet(x), SingletonSet(y), x)(xy) join
          singletonEquals(x, y)(sx)(sy)
          )(equalsReflexive(x))
      }

      val <~ = assume(x === y) { xy =>
        val (f, setFa) = zEqPair(SingletonSet(x), SingletonSet(y))
        equalsIff2(SingletonSet(x), SingletonSet(y))(
          singletonMembershipCommutative(f, x)(setFa)(sx) join
            axiomT(x, y, SingletonSet(f))(xy) join
            singletonMembershipCommutative(y, f)(sy)(setFa)
        )
      }

      ~> combine <~
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
      equalsSymmetric((
        iffCommutative(axiomP(x, y, x)(sx)(sy)(sx)) join
          iffCommutative(equalsIff1(SingletonSet(z), PairSet(x, y), x)(hyp)) join
          singletonEquals(x, z)(sx)(sz)
        )(equalsReflexive(x) #\/ (x === y)))
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

  implicit class WrapperIntersect[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, Intersect[X, Y]]]) {
    def toIff(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, X] /\ Member[Z, Y]] = intersectIff(thm.b.a, thm.b.b, thm.a)(sz)(thm)
  }

  implicit class WrapperUnion[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, Union[X, Y]]]) {
    def toIff(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, X] \/ Member[Z, Y]] = unionContains(thm.b.a, thm.b.b, thm.a)(sz)(thm)
  }

  implicit class WrapperDifference[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, Difference[X, Y]]]) {
    def toIff(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, X] /\ ~[Member[Z, Y]]] = differenceContains(thm.b.a, thm.b.b, thm.a)(sz)(thm)
  }

  implicit class WrapperComplement[X <: AnySet, Y <: AnySet](thm: Theorem[Member[Y, Complement[X]]]) {
    def toIff(sy: Theorem[IsSet[Y]]): Theorem[~[Member[Y, X]]] = complementIff(thm.b.a, thm.a)(sy)(thm)
  }

  implicit class WrapperIntersectIff[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, X] /\ Member[Z, Y]]) {
    def toIntersect(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, Intersect[X, Y]]] = intersectIff(thm.x.b, thm.y.b, thm.x.a)(sz).swap(thm)
  }

  implicit class WrapperUnionIff[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, X] \/ Member[Z, Y]]) {
    def toIntersect(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, Union[X, Y]]] = unionContains(thm.x.b, thm.y.b, thm.x.a)(sz).swap(thm)
  }

  implicit class WrapperDifferenceIff[X <: AnySet, Y <: AnySet, Z <: AnySet](thm: Theorem[Member[Z, X] /\ ~[Member[Z, Y]]]) {
    def toIntersect(sz: Theorem[IsSet[Z]]): Theorem[Member[Z, Difference[X, Y]]] = differenceContains(thm.x.b, thm.y.x.b, thm.x.a)(sz).swap(thm)
  }

  implicit class WrapperComplementIff[X <: AnySet, Y <: AnySet](thm: Theorem[~[Member[Y, X]]]) {
    def toIntersect(sy: Theorem[IsSet[Y]]): Theorem[Member[Y, Complement[X]]] = complementIff(thm.x.b, thm.x.a)(sy).swap(thm)
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
  def subsetUnion[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[X, Y] <-> (Union[X, Y] === Y)] = {
    val ~> = assume(x sube y) { hyp =>
      val (z, sz) = zEqPair(x union y, y)
      val ~> = assume((z in x) \/ (z in y))(_.reduce(subsetEqIff1(x, y, z)(hyp))(assume(z in y)(identity)))
      val <~ = assume(z in y)((z in x) #\/ _)
      (unionContains(x, y, z)(sz) join (~> combine <~)).toEquals
    }
    val <~ = assume((x union y) === y) { hyp =>
      val (z, sz) = (SkolemFunction2[FB, X, Y](x, y), isSetFb(x, y))
      subsetEqIff2(x, y)(assume(z in x)(h => (unionContains(x, y, z)(sz).swap join hyp.toImplies(z))(h #\/ (z in y))))
    }

    ~> combine <~
  }

  /** `(x inter y) inter z = x inter (y inter z)` */
  def intersectAssociative[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Intersect[Intersect[X, Y], Z] === Intersect[X, Intersect[Y, Z]]] = {
    val (w, sw) = zEqPair((x inter y) inter z, x inter (y inter z))

    val ~> = assume(w in ((x inter y) inter z)) { hyp =>
      val (txy, tz) = intersectIff(x inter y, z, w)(sw)(hyp).asPair
      val (tx, ty) = intersectIff(x, y, w)(sw)(txy).asPair
      intersectIff(x, y inter z, w)(sw).swap(tx #/\ intersectIff(y, z, w)(sw).swap(ty #/\ tz))
    }
    val <~ = assume(w in (x inter (y inter z))) { hyp =>
      val (tx, tyz) = intersectIff(x, y inter z, w)(sw)(hyp).asPair
      val (ty, tz) = intersectIff(y, z, w)(sw)(tyz).asPair
      intersectIff(x inter y, z, w)(sw).swap(intersectIff(x, y, w)(sw).swap(tx #/\ ty) #/\ tz)
    }

    (~> combine <~).toEquals
  }

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
  def unionEmpty[X <: AnySet](x: X): Theorem[Union[X, EmptySet] === X] = {
    val (z, sz) = zEqPair(x union EmptySet, x)

    val ~> = assume((z in x) \/ (z in EmptySet))(hyp => mixedDoubleNegationInvert(swapAssumptions(orImplies(hyp))(axiomN(z)(sz))))
    val <~ = assume(z in x)(hyp => orAddRight(hyp, z in EmptySet))

    equalsIff2(x union EmptySet, x)(iffTransitive(unionContains(x, EmptySet, z)(sz), impliesToIffRule(~>, <~)))
  }

  /** `(x inter U) = x` */
  def intersectUniverse[X <: AnySet](x: X): Theorem[Intersect[X, Universe] === X] = {
    val (z, sz) = zEqPair(x inter Universe, x)

    val ~> = assume((z in x) /\ (z in Universe))(andExtractLeft)
    val <~ = assume(z in x)(hyp => andCombine(hyp, universeContains(z)(sz)))

    equalsIff2(x inter Universe, x)(iffTransitive(intersectIff(x, Universe, z)(sz), impliesToIffRule(~>, <~)))
  }

  /** `(x union U) = U` */
  def unionUniverse[X <: AnySet](x: X): Theorem[Union[X, Universe] === Universe] = {
    val (z, sz) = zEqPair(x union Universe, Universe)

    val t = universeContains(z)(sz)
    val ~> = assume((z in x) \/ (z in Universe))(_ => t)
    val <~ = assume(z in Universe)(_ => orCommutative(orAddRight(t, z in x)))

    equalsIff2(x union Universe, Universe)(iffTransitive(unionContains(x, Universe, z)(sz), impliesToIffRule(~>, <~)))
  }

  /** `-(x union y) = (-x inter -y)` */
  def unionComplement[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[-[Union[X, Y]] === Intersect[-[X], -[Y]]] = {
    val (z, sz) = zEqPair(-(x union y), -x inter -y)

    val ~> = assume(z in -(x union y)) { hyp =>
      val t = unionContains(x, y, z)(sz).swap.toImplies join complementIff(x union y, z)(sz)(hyp).toImplies
      val l = complementIff(x, z)(sz).swap(assume(z in x)(h => t(h #\/ (z in y))).toNot)
      val r = complementIff(y, z)(sz).swap(assume(z in y)(h => t((z in x) #\/ h)).toNot)
      intersectIff(-x, -y, z)(sz).swap(l #/\ r)
    }
    val <~ = assume(z in (-x inter -y)) { hyp =>
      val (l, r) = intersectIff(-x, -y, z)(sz)(hyp).asPair
      val la = complementIff(x, z)(sz)(l)
      val ra = complementIff(y, z)(sz)(r)
      complementIff(x union y, z)(sz).swap((unionContains(x, y, z)(sz).toImplies join orIff(z in x, z in y).toImplies join #~~(la #/\ ra).toImplies).toNot)
    }

    (~> combine <~).toEquals
  }

  /** `-(x inter y) = (-x union -y)` */
  def intersectComplement[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[-[Intersect[X, Y]] === Union[-[X], -[Y]]] = {
    val (z, sz) = zEqPair(-(x union y), -x inter -y)

    val ~> = assume(z in -(x inter y)) { hyp =>
      val t1 = hyp.toIff(sz).map(intersectIff(x, y, z)(sz).swap.toImplies).toImplies
      ???
    }
    val <~ = assume(z in (-x union -y)) { hyp =>
      val t1 = hyp.toIff(sz).mapLeft(complementIff(x, z)(sz).toImplies).mapRight(complementIff(y, z)(sz).toImplies)
      val t2 = orImplies(t1)
      val t3 = assume(z in x)(zx => assume(z in y)(zy => t2(#~~(zx))(#~~(zy))))
      ???
    }

    //(~> combine <~).toEquals
    ???
  }

  /** `(x diff x) = {}` */
  def differenceSelf[X <: AnySet](x: X): Theorem[Difference[X, X] === EmptySet] = {
    val (z, sz) = zEqPair(x diff x, EmptySet)

    val ~> = assume((z in x) /\ ~(z in x))(hyp => exFalso(z in EmptySet)(notIff(z in x)(andExtractLeft(andCommutative(hyp)))(andExtractLeft(hyp))))
    val <~ = assume(z in EmptySet)(hyp => exFalso((z in x) /\ ~(z in x))(notIff(z in EmptySet)(axiomN(z)(sz))(hyp)))

    equalsIff2(x diff x, EmptySet)(iffTransitive(differenceContains(x, x, z)(sz), impliesToIffRule(~>, <~)))
  }

  /** `(U diff x) = -x` */
  def universeDifference[X <: AnySet](x: X): Theorem[Difference[Universe, X] === -[X]] = {
    val (z, sz) = zEqPair(Universe diff x, -x)

    val ~> = assume((z in Universe) /\ ~(z in x))(hyp => andExtractLeft(andCommutative(hyp)))
    val <~ = assume(~(z in x))(hyp => andCombine(universeContains(z)(sz), hyp))

    equalsIff2(Universe diff x, -x)(iffTransitive(iffTransitive(differenceContains(Universe, x, z)(sz), impliesToIffRule(~>, <~)), iffCommutative(complementIff(x, z)(sz))))
  }

  /** `x diff (x diff y) = (x inter y)` */
  def doubleDifference[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Difference[X, Difference[X, Y]] === Intersect[X, Y]] = ???

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
  def intersectDistributivity[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Intersect[X, Union[Y, Z]] === Union[Intersect[X, Y], Intersect[X, Z]]] = ???

  /** `x union (y inter z) = (x union y) inter (x union z)` */
  def unionDistributivity[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[Union[X, Intersect[Y, Z]] === Intersect[Union[X, Y], Union[X, Z]]] = ???


  /** `U({}) = {}` */
  def sumEmpty: Theorem[Sum[EmptySet] === EmptySet] = {
    val (z, sz) = zEqPair(Sum(EmptySet), EmptySet)
    val sq = isSetQ(EmptySet, z)

    val ~> = assume(z in Sum(EmptySet))(hyp => axiomN(sq.s)(sq).toImplies(sumIff1(EmptySet, z)(sz)(hyp).right)(z in EmptySet))
    val <~ = assume(z in EmptySet)(hyp => axiomN(z)(sz).toImplies(hyp)(z in Sum(EmptySet)))

    (~> combine <~).toEquals
  }

  /** `M(x) -> U({x}) = x` */
  def sumSingleton[X <: AnySet](x: X): Theorem[IsSet[X] ->: (Sum[SingletonSet[X]] === X)] = assume(IsSet(x)) { sx =>
    val (z, sz) = zEqPair(Sum(SingletonSet(x)), x)
    val sq = isSetQ(SingletonSet(x), z)

    val ~> = assume(z in Sum(SingletonSet(x))) { hyp =>
      val (zq, qsx) = sumIff1(SingletonSet(x), z)(sz)(hyp).asPair
      singletonEquals(sq.s, x)(sq)(sx)(qsx).toImplies(z)(zq)
    }
    val <~ = assume(z in x)(hyp => sumIff2(SingletonSet(x), x, z)(sx)(sz)(hyp #/\ singletonEquals(x, x)(sx)(sx).swap(x.reflexive)))

    (~> combine <~).toEquals
  }

  /** `Sum({{}}) = {}` */
  def sumSingletonEmpty: Theorem[Sum[SingletonSet[EmptySet]] === EmptySet] = sumSingleton(EmptySet)(axiomNS) // Corollary

  /** `U(V) = V` */
  def sumUniverse: Theorem[Sum[Universe] === Universe] = {
    val (z, sz) = zEqPair(Sum(Universe), Universe)

    val ~> = assume(z in Sum(Universe))(_ => universeContains(z)(sz))
    val <~ = assume(z in Universe) { _ =>
      val y = SingletonSet(z)
      val sy = singletonIsSet(sz)
      sumIff2(Universe, y, z)(sy)(sz)(singletonEquals(z, z)(sz)(sz).swap(z.reflexive) #/\ universeContains(y)(sy))
    }

    (~> combine <~).toEquals
  }

  /** `P(V) = V` */
  def powerUniverse: Theorem[Power[Universe] === Universe] = {
    val (z, sz) = zEqPair(Power(Universe), Universe)

    val ~> = assume(z in Power(Universe))(_ => universeContains(z)(sz))
    val <~ = assume(z in Universe)(_ => powerIff(z, Universe)(sz).swap(subsetEqUniverse(z)))

    (~> combine <~).toEquals
  }


  /** `x sube x` */
  def subsetEqReflexive[X <: AnySet](x: X): Theorem[SubsetEqual[X, X]] = {
    val z = isSetFb(x, x).s
    subsetEqIff2(x, x)(assume(z in x)(identity))
  }

  /** `{} sube x` */
  def emptySubsetEq[X <: AnySet](x: X): Theorem[SubsetEqual[EmptySet, X]] = {
    val sz = isSetFb(EmptySet, x)
    val z = sz.s
    subsetEqIff2(EmptySet, x)(assume(z in EmptySet)(hyp => axiomN(z)(sz).toImplies(hyp)(z in x)))
  }

  /** `x sube {} <-> x = {}` */
  def subsetEqEmpty[X <: AnySet](x: X): Theorem[SubsetEqual[X, EmptySet] <-> (X === EmptySet)] = {
    val ~> = assume(x sube EmptySet) { hyp =>
      val (z, sz) = zEqPair(x, EmptySet)
      val ~> = subsetEqIff1(x, EmptySet, z)(hyp)
      val <~ = assume(z in EmptySet)(h => axiomN(z)(sz).toImplies(h)(z in x))
      (~> combine <~).toEquals
    }
    val <~ = assume(x === EmptySet) { hyp =>
      val z = isSetFb(x, EmptySet).s
      subsetEqIff2(x, EmptySet)(hyp.toImplies(z).toImplies)
    }

    ~> combine <~
  }

  /** `x sube U` */
  def subsetEqUniverse[X <: AnySet](x: X): Theorem[SubsetEqual[X, Universe]] = {
    val sb = isSetFb(x, Universe)
    val b = sb.s
    subsetEqIff2(x, Universe)(assume(b in x)(_ => universeContains(b)(sb)))
  }

  /** `(x sube y) -> (y sube z) -> (x sube z)` */
  def subsetEqTransitivity[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[SubsetEqual[X, Y] ->: SubsetEqual[Y, Z] ->: SubsetEqual[X, Z]] = assume(x sube y, y sube z) { (xy, yz) =>
    val sb = isSetFb(x, z)
    val b = sb.s
    subsetEqIff2(x, z)(subsetEqIff1(x, y, b)(xy) join subsetEqIff1(y, z, b)(yz))
  }

  /** `z sube (x inter y) <-> ((z sube x) /\ (z sube y))` */
  def subsetEqInter[X <: AnySet, Y <: AnySet, Z <: AnySet](x: X, y: Y, z: Z): Theorem[SubsetEqual[Z, Intersect[X, Y]] <-> (SubsetEqual[Z, X] /\ SubsetEqual[Z, Y])] = {
    val ~> = assume(z sube (x inter y)) { hyp =>
      val sbx = isSetFb(z, x)
      val bx = sbx.s
      val sby = isSetFb(z, y)
      val by = sby.s

      val l = subsetEqIff2(z, x)(subsetEqIff1(z, x inter y, bx)(hyp) join intersectIff(x, y, bx)(sbx).toImplies join assume((bx in x) /\ (bx in y))(_.left))
      val r = subsetEqIff2(z, y)(subsetEqIff1(z, x inter y, by)(hyp) join intersectIff(x, y, by)(sby).toImplies join assume((by in x) /\ (by in y))(_.right))

      l #/\ r
    }
    val <~ = assume((z sube x) /\ (z sube y)) { hyp =>
      val sb = isSetFb(z, x inter y)
      val b = sb.s

      val (l, r) = hyp.asPair

      subsetEqIff2(z, x inter y)(assume(b in z)(h => intersectIff(x, y, b)(sb).swap(subsetEqIff1(z, x, b)(l)(h) #/\ subsetEqIff1(z, y, b)(r)(h))))
    }

    ~> combine <~
  }

  /** `M(x) -> (x in P(x))` */
  def powerMonoticity[X <: AnySet](x: X): Theorem[IsSet[X] ->: Member[X, Power[X]]] = assume(IsSet(x)) { sx =>
    powerIff(x, x)(sx).swap(subsetEqReflexive(x))
  }

  /** `(x sube y) -> (U(x) sube U(y))` */
  def sumSubsetEqMonotonicity[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[X, Y] ->: SubsetEqual[Sum[X], Sum[Y]]] = assume(x sube y) { hyp =>
    val sb = isSetFb(Sum(x), Sum(y))
    val b = sb.s
    val sq = isSetQ(x, b)
    val q = sq.s
    subsetEqIff2(Sum(x), Sum(y))(assume(b in Sum(x))(h => sumIff2(y, q, b)(sq)(sb)(sumIff1(x, b)(sb)(h).mapRight(subsetEqIff1(x, y, q)(hyp)))))
  }

  /** `(x sube y) -> (P(x) sube P(y))` */
  def powerSubsetEqMonoticity[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[SubsetEqual[X, Y] ->: SubsetEqual[Power[X], Power[Y]]] = assume(x sube y) { hyp =>
    val sb = isSetFb(Power(x), Power(y))
    val b = sb.s
    subsetEqIff2(Power(x), Power(y))(assume(b in Power(x))(h => powerIff(b, y)(sb).swap(subsetEqTransitivity(b, x, y)(powerIff(b, x)(sb)(h))(hyp))))
  }

  /** `U(P(x)) = x` */
  def sumPower[X <: AnySet](x: X): Theorem[IsSet[X] ->: (Sum[Power[X]] === X)] = assume(IsSet(x)) { sx =>
    val (z, sz) = zEqPair(Sum(Power(x)), x)

    val ~> = assume(z in Sum(Power(x))) { hyp =>
      val (zq, qpx) = sumIff1(Power(x), z)(sz)(hyp).asPair
      val sq = isSetQ(Power(x), z)
      val q = sq.s
      subsetEqIff1(q, x, z)(powerIff(q, x)(sq)(qpx))(zq)
    }
    val <~ = assume(z in x) { hyp =>
      sumIff2(Power(x), x, z)(sx)(sz)(hyp #/\ powerMonoticity(x)(sx))
    }

    (~> combine <~).toEquals
  }

  /** `x sube P(U(x))` */
  def powerSum[X <: AnySet](x: X): Theorem[SubsetEqual[X, Power[Sum[X]]]] = {
    val sb = isSetFb(x, Power(Sum(x)))
    val b = sb.s
    val sb1 = isSetFb(b, Sum(x))
    val b1 = sb1.s

    subsetEqIff2(x, Power(Sum(x)))(assume(b in x)(hyp => powerIff(b, Sum(x))(sb).swap(subsetEqIff2(b, Sum(x))(assume(b1 in b)(_ #/\ hyp) join sumIff2(x, b, b1)(sb)(sb1)))))
  }

  /** `P(x inter y) = P(x) inter P(y)` */
  def powerIntersect[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[Power[Intersect[X, Y]] === Intersect[Power[X], Power[Y]]] = {
    val (z, sz) = zEqPair(Power(x inter y), Power(x) inter Power(y))

    val ~> = assume((z sube x) /\ (z sube y))(h => powerIff(z, x)(sz).swap(h.left) #/\ powerIff(z, y)(sz).swap(h.right))
    val <~ = assume((z in Power(x)) /\ (z in Power(y)))(h => powerIff(z, x)(sz)(h.left) #/\ powerIff(z, y)(sz)(h.right))

    (powerIff(z, x inter y)(sz) join subsetEqInter(x, y, z) join (~> combine <~) join intersectIff(Power(x), Power(y), z)(sz).swap).toEquals
  }

  /** `P({}) = {{}}` */
  def powerEmpty: Theorem[Power[EmptySet] === SingletonSet[EmptySet]] = {
    val (z, sz) = zEqPair(Power(EmptySet), SingletonSet(EmptySet))
    (powerIff(z, EmptySet)(sz) join subsetEqEmpty(z) join singletonEquals(z, EmptySet)(sz)(axiomNS).swap).toEquals
  }

  /** `P({{}}) = {{}, {{}}}` */
  def powerSingletonEmpty: Theorem[Power[SingletonSet[EmptySet]] === PairSet[EmptySet, SingletonSet[EmptySet]]] = {
    val (z, sz) = zEqPair(Power(SingletonSet(EmptySet)), PairSet(EmptySet, SingletonSet(EmptySet)))

    val ~> = assume(z in Power(SingletonSet(EmptySet))) { hyp =>
      val (z2, sz2) = zEqPair(z, SingletonSet(EmptySet))

      val t1 = powerIff(z, SingletonSet(EmptySet))(sz)(hyp)
      val l = subsetEqIff1(z, SingletonSet(EmptySet), z2)(t1) join singletonEquals(z2, EmptySet)(sz2)(axiomNS).toImplies

      assume(~(z === EmptySet)) { h1 =>
        assume(~(z === SingletonSet(EmptySet))) { h2 =>
          val t1 = powerIff(z, SingletonSet(EmptySet))(sz)(hyp)
          val l = subsetEqIff1(z, SingletonSet(EmptySet), z2)(t1) join singletonEquals(z2, EmptySet)(sz2)(axiomNS).toImplies

          ???
        }
      }

      oops(z in PairSet(EmptySet, SingletonSet(EmptySet)))
    }
    val <~ = assume(z in PairSet(EmptySet, SingletonSet(EmptySet))) { hyp =>
      val sb = isSetFb(z, SingletonSet(EmptySet))
      val b = sb.s

      val ~> = assume(b in z) { h1 =>
        val l = assume(z === EmptySet)(h2 => axiomN(b)(sb).toImplies(h2.toImplies(b)(h1))(b in SingletonSet(EmptySet)))
        val r = assume(z === SingletonSet(EmptySet))(h2 => h2.toImplies(b)(h1))
        axiomP(EmptySet, SingletonSet(EmptySet), z)(axiomNS)(singletonIsSet(axiomNS))(sz)(hyp).reduce(l)(r)
      }
      powerIff(z, SingletonSet(EmptySet))(sz).swap(subsetEqIff2(z, SingletonSet(EmptySet))(~>))
    }

    //(~> combine <~).toEquals
    ???
  }
}
