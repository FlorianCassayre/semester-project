package solver

import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._
import theory.NBGTheory._
import theory.NBGRules._
import theory.NBGTheorems._
import theory.NBGTheory

object Tableaux {

  def prove[P <: Formula](p: P): Option[Theorem[P]] = {
    // https://en.wikipedia.org/wiki/Method_of_analytic_tableaux

    type AnyTheorem = Theorem[_ <: Formula]

    // Transparent helper types
    type X = Formula
    type Y = Formula

    type Q = AnySet
    type R = AnySet
    type S = AnySet

    // Normally a union type between False and True
    type Result = Formula

    case class Facts(
                      map: Map[Formula, AnyTheorem] = Map.empty,
                      equalitiesLeftArg: Map[AnySet, Set[Theorem[Equals[_ <: AnySet, _ <: AnySet]]]] = Map.empty,
                      membershipsRightArg: Map[AnySet, Set[Theorem[Member[_ <: AnySet, _ <: AnySet]]]] = Map.empty,
                      notMembershipsRightArg: Map[AnySet, Set[Theorem[_ <: ~[Member[AnySet, AnySet]]]]] = Map.empty
    ) {
      def withTheorem(thm: AnyTheorem): Facts = {
        val updatedMap = map + (thm.formula -> thm)
        thm.formula match {
          case x === y =>
            val t = thm.as[R === S]
            val ts = t.swap
            val firstUpdate = equalitiesLeftArg + (x -> (equalitiesLeftArg.getOrElse(x, Set.empty) + t))
            val secondUpdate = firstUpdate + (y -> (firstUpdate.getOrElse(y, Set.empty) + ts))
            copy(map = updatedMap + (ts.formula -> ts), equalitiesLeftArg = secondUpdate)
          case Member(x, y) =>
            val t = thm.as[Member[Q, R]]
            val ss = isSetIff2(x, y)(t)
            copy(map = updatedMap + (ss.formula -> ss),
            membershipsRightArg = membershipsRightArg + (y -> (membershipsRightArg.getOrElse(y, Set.empty) + t))
          )
          case ~(Member(x, y)) => copy(map = updatedMap,
            notMembershipsRightArg = notMembershipsRightArg + (y -> (notMembershipsRightArg.getOrElse(y, Set.empty) + thm.as[~[Member[Q, R]]]))
          )
          case other => copy(map = updatedMap)
        }
      }
    }

    def result(f: Result): Boolean = f match {
      case False => false
      case True => true
    }

    def tableaux(facts: Facts, thms: Seq[AnyTheorem]): Theorem[Result] = {
      def alphaConsequence[L <: Formula, R <: Formula](and: Theorem[L /\ R]): Theorem[Result] = {
        val (left, right) = and.asPair
        tableaux(facts, left +: right +: thms.tail)
      }
      def betaBranch[L <: Formula, R <: Formula](or: Theorem[L \/ R]): Theorem[Result] = {
        val l = assume(or.x)(t => tableaux(facts, t +: thms.tail))
        val r = assume(or.y)(t => tableaux(facts, t +: thms.tail))
        if(result(l.y) || result(r.y)) {
          truth
        } else {
          or.reduce(l)(r)
        }
      }

      def proveIsSet(set: AnySet): Option[Theorem[IsSet[AnySet]]] = set match {
        case EmptySet => Some(axiomNS.as[IsSet[AnySet]])
        case PairSet(a, b) => for(sa <- proveIsSet(a); sb <- proveIsSet(b)) yield axiomPS(sa.s, sb.s)(sa)(sb).as[IsSet[AnySet]]
        case SingletonSet(a) => for(sa <- proveIsSet(a)) yield singletonIsSet(sa).as[IsSet[AnySet]]
        case OrderedPair(a, b) => for(sa <- proveIsSet(a); sb <- proveIsSet(b)) yield orderedPairSet(sa.s, sb.s)(sa)(sb).as[IsSet[AnySet]]
        case Intersect(a, b) => proveIsSet(a).map(sa => equalsIsSet(intersectSet(a, b)(sa) #/\ intersectCommutative(a, b)).as[IsSet[AnySet]])
          .orElse(proveIsSet(b).map(sb => intersectSet(a, b)(sb).as[IsSet[AnySet]]))
        case Union(a, b) => for(sa <- proveIsSet(a); sb <- proveIsSet(b)) yield unionSet(sa.s, sb.s)(sa)(sb).as[IsSet[AnySet]]
        case f@SkolemFunction2(a, b) if f.name == valueOf[FA] => Some(isSetFa(a, b).as[IsSet[AnySet]])
        case other => facts.map.get(IsSet(other)).map(_.as[IsSet[AnySet]])
      }

      thms match {
        case thm +: tail =>

          thm.formula match {
            case atom if facts.map.contains(~atom) => facts.map(~atom).as[~[X]].toImplies(thm)
            case p /\ q => alphaConsequence(thm.as[X /\ Y])
            case p \/ q => betaBranch(thm.as[X \/ Y])
            case p ->: q => betaBranch(impliesToOr(thm.as[X ->: Y]))
            case p <-> q =>
              val t = thm.as[X <-> Y]
              alphaConsequence(t.toImplies #/\ t.swap.toImplies)
            case False => thm.as[False]
            case True => tableaux(facts, tail)
            case ~(~(p)) => tableaux(facts, thm.as[~[~[P]]].unduplicate +: tail)
            case SubsetEqual(x, y) => tableaux(facts, subsetIntersect(x, y)(thm.as[SubsetEqual[R, S]]) +: tail)
            case Member(z, Complement(x)) => tableaux(facts, thm.as[Member[Q, -[R]]].toIff +: tail)
            case Member(z, Intersect(x, y)) => alphaConsequence(thm.as[Member[Q, Intersect[R, S]]].toIff)
            case Member(z, Union(x, y)) => betaBranch(thm.as[Member[Q, Union[R, S]]].toIff)
            case Member(z, Difference(x, y)) => alphaConsequence(thm.as[Member[Q, Difference[R, S]]].toIff)
            case Member(z, EmptySet) =>
              val t = thm.as[Member[Q, EmptySet]]
              axiomN(z)(t.asSet).toImplies(t)
            case Member(z, SingletonSet(x)) => tableaux(facts, singletonEq(x).toIff(z)(thm.as[Member[Q, SingletonSet[R]]]) +: tail)
            case Member(z, PairSet(x, y)) =>
              val t = thm.as[Member[Q, PairSet[R, S]]]
              val opt = for(sx <- proveIsSet(x); sy <- proveIsSet(y)) yield betaBranch(axiomP(x, y, z)(sx)(sy)(isSetIff2(z, PairSet(x, y))(t))(t))
              opt.getOrElse(tableaux(facts.withTheorem(thm), tail))
            case Member(z, OrderedPair(x, y)) => tableaux(facts, orderedPairEq(x, y).toIff(z)(thm.as[Member[Q, OrderedPair[R, S]]]) +: tail)
            case Member(z, Universe) => tableaux(facts.withTheorem(thm), tail)
            case x === y if !facts.map.contains(thm.formula) && facts.membershipsRightArg.contains(x) =>
              val eq = thm.as[R === S]
              val mbs = facts.membershipsRightArg(x).map(_.as[Member[Q, R]])
              tableaux(facts.withTheorem(eq), mbs.map(mb => equalsIff1(x, y, mb.a)(eq)(mb)).toSeq ++ tail)
            case Member(x, y) if !facts.map.contains(thm.formula) && facts.equalitiesLeftArg.contains(y) =>
              val mb = thm.as[Member[Q, R]]
              val eqs = facts.equalitiesLeftArg(y).map(_.as[R === S])
              tableaux(facts.withTheorem(mb), eqs.map(eq => equalsIff1(y, eq.b, x)(eq)(mb)).toSeq ++ tail)
            case Member(x, y) if !facts.map.contains(thm.formula) && facts.notMembershipsRightArg.contains(y) =>
              val l = thm.as[Member[R, Q]]
              val rs = facts.notMembershipsRightArg(y).map(_.as[~[Member[S, Q]]])
              tableaux(facts.withTheorem(l), rs.map { ri =>
                val (q, r, s) = (l.b, l.a, ri.x.a)
                axiomT(r, s, q).inverse(assume((r in q) <-> (s in q))(h => ri.toImplies(h(l))).toNot)
              }.toSeq ++ tail)
            case ~(f) =>
              f match {
                case atom if facts.map.contains(atom) => thm.as[~[X]].toImplies(facts.map(atom))
                case p /\ q => betaBranch(notAnd(thm.as[~[X /\ Y]]))
                case p \/ q => alphaConsequence(notOr(thm.as[~[~[X] \/ ~[Y]]]))
                case p ->: q => alphaConsequence(notOr(thm.as[~[X ->: Y]].map(assume(~p \/ q)(h => orToImplies(h)))).mapLeft(_.unduplicate))
                case p <-> q => betaBranch(notAnd(assume((p ->: q) /\ (q ->: p))(h => thm.as[~[X <-> Y]].toImplies(h.left combine h.right)).toNot))
                case False => tableaux(facts, tail)
                case True => thm.as[~[True]].toImplies(truth)
                case SubsetEqual(x, y) => tableaux(facts, subsetIntersect(x, y).inverse(thm.as[~[SubsetEqual[R, S]]]) +: tail)
                case Member(z, Complement(x)) => betaBranch(notDefinition(complementIff(x, z), thm.as[~[Member[Q, -[R]]]]))
                case Member(z, Intersect(x, y)) => betaBranch(notDefinition(intersectIff(x, y, z), thm.as[~[Member[Q, Intersect[R, S]]]]))
                case Member(z, Union(x, y)) => betaBranch(notDefinition(unionContains(x, y, z), thm.as[~[Member[Q, Union[R, S]]]]))
                case Member(z, Difference(x, y)) => betaBranch(notDefinition(differenceContains(x, y, z), thm.as[~[Member[Q, Difference[R, S]]]]))
                case Member(z, EmptySet) => tableaux(facts.withTheorem(thm), tail)
                case Member(z, SingletonSet(x)) => tableaux(facts, singletonEq(x).toIff(z).inverse(thm.as[~[Member[Q, SingletonSet[R]]]]) +: tail)
                case Member(z, PairSet(x, y)) =>
                  val t = thm.as[~[Member[Q, PairSet[R, S]]]]
                  val opt = for(sx <- proveIsSet(x); sy <- proveIsSet(y); sz <- proveIsSet(z)) yield alphaConsequence(axiomP(x, y, z)(sx)(sy)(sz).inverse(t).toAndNot)
                  opt.getOrElse(tableaux(facts.withTheorem(thm), tail))
                case Member(z, OrderedPair(x, y)) => tableaux(facts, orderedPairEq(x, y).toIff(z).inverse(thm.as[~[Member[Q, OrderedPair[R, S]]]]) +: tail)
                case Member(z, Universe) => tableaux(facts, universeContains(z).inverse(thm.as[~[Member[Q, Universe]]]) +: tail)
                case x === y =>
                  val t = equalsIff2(x, y)
                  tableaux(facts, equalsIff2(x, y).inverse(thm.as[~[R === S]]) +: tail)
                case Member(x, y) if !facts.map.contains(thm.formula) && facts.membershipsRightArg.contains(y) =>
                  val ls = facts.membershipsRightArg(y).map(_.as[Member[R, Q]])
                  val ri = thm.as[~[Member[S, Q]]]
                  tableaux(facts.withTheorem(ri), ls.map { l =>
                    val (q, r, s) = (ri.x.b, l.a, ri.x.a)
                    axiomT(r, s, q).inverse(assume((r in q) <-> (s in q))(h => ri.toImplies(h(l))).toNot)
                  }.toSeq ++ tail)
                case IsSet(x) =>
                  proveIsSet(x).map(skolem => thm.as[~[IsSet[_ <: AnySet]]].toImplies(skolem))
                      .getOrElse(tableaux(facts.withTheorem(thm), tail))
                case _ => tableaux(facts.withTheorem(thm), tail)
              }
            case _ => tableaux(facts.withTheorem(thm), tail)
              // Here would go the cut rule
          }

        case _ => truth // No more inputs
      }
    }

    val res = assume(~p)(np => tableaux(Facts(), Seq(np)))
    if(result(res.y)) {
      None
    } else {
      Some(mixedDoubleNegationInvert(res.as[~[P] ->: False]))
    }
  }
}
