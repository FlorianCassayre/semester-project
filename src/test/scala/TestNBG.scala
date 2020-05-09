import org.scalatest.Ignore
import org.scalatest.funsuite.AnyFunSuite
import theory.NBGTheorems

class TestNBG extends ProofTestSuite with NBGTheorems {

  val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])
  val (x, y, z, u, v) = (SetVariable["x"], SetVariable["y"], SetVariable["z"], SetVariable["u"], SetVariable["v"])
  type W = "w"
  val id: W = implicitly[ValueOf[W]].value
  val w: SetVariable[W] = SetVariable(id)

  test("equals subset") {
    equalsSubset(x, y) =?= ((x === y) <-> ((x sube y) /\ (y sube x)))
  }

  test("equals reflexive") {
    equalsReflexive(x) =?= (x === x)
  }

  test("equals symmetric") {
    equalsSymmetric(x === y) =?= (y === x)
  }

  test("equals transitive") {
    equalsTransitive(x === y, y === z) =?= (x === z)
  }

  test("equals symmetric iff") {
    equalsSymmetricIff(x, y) =?= (x === y) <-> (y === x)
  }

  test("equals all iff") {
    val a = SkolemFunction2[FA, SetVariable["x"], SetVariable["y"]](x, y)
    equalsAllIff(x, y) =?= (x === y) <-> ((a in x) <-> (a in y))
  }

  test("equals is set") {
    equalsIsSet(IsSet(z) /\ (z === y)) =?= IsSet(y)
  }

  test("pair commutative") {
    pairCommutative(x, y) =?= (IsSet(x) ->: IsSet(y) ->: (PairSet(x, y) === PairSet(y, x)))
  }

  test("singleton equals") {
    singletonEquals(x, y) =?= IsSet(x) ->: IsSet(y) ->: ((x in SingletonSet(y)) <-> (x === y))
  }

  test("singleton membership commutative") {
    singletonMembershipCommutative(x, y) =?= IsSet(x) ->: IsSet(y) ->: ((x in SingletonSet(y)) <-> (y in SingletonSet(x)))
  }

  test("singleton congruence") {
    singletonCongruence(x, y) =?= (IsSet(x) ->: IsSet(y) ->: ((SingletonSet(x) === SingletonSet(y)) <-> (x === y)))
  }

  test("ordered pair to equals") {
    orderedPairToEquals(x, y, u, v) =?= IsSet(x) ->: IsSet(y) ->: IsSet(u) ->: IsSet(v) ->: (OrderedPair(x, y) === OrderedPair(u, v)) ->: ((x === u) /\ (y === v))
  }

  test("union contains") {
    unionContains(x, y, z) =?= IsSet(z) ->: ((z in (x union y)) <-> ((z in x) \/ (z in y)))
  }

  test("universe contains") {
    universeContains(x) =?= IsSet(x) ->: (x in Universe)
  }

  test("difference contains") {
    differenceContains(x, y, z) =?= IsSet(z) ->: ((z in (x diff y)) <-> ((z in x) /\ ~(z in y)))
  }

  test("intersect commutative") {
    intersectCommutative(x, y) =?= ((x inter y) === (y inter x))
  }

  test("complement congruence") {
    complementCongruence(x, y) =?= ((x === y) <-> (-x === -y))
  }

  test("union commutative") {
    unionCommutative(x, y) =?= ((x union y) === (y union x))
  }

  test("subset intersection") {
    subsetIntersect(x, y) =?= ((x sube y) <-> ((x inter y) === x))
  }

  test("subset union") {
    subsetUnion(x, y) =?= ((x sube y) <-> ((x union y) === y))
  }

  test("intersection associative") {
    intersectAssociative(x, y, z) =?= (((x inter y) inter z) === (x inter (y inter z)))
  }

  ignore("union associative") {
    unionAssociative(x, y, z) =?= (((x union y) union z) === (x union (y union z)))
  }

  test("intersection indempotent") {
    intersectIndempotent(x) =?= ((x inter x) === x)
  }

  test("union indempotent") {
    unionIndempotent(x) =?= ((x union x) === x)
  }

  test("intersection empty") {
    intersectEmpty(x) =?= ((x inter EmptySet) === EmptySet)
  }

  test("union empty") {
    unionEmpty(x) =?= ((x union EmptySet) === x)
  }

  test("intersection universe") {
    intersectUniverse(x) =?= ((x inter Universe) === x)
  }

  test("union universe") {
    unionUniverse(x) =?= ((x union Universe) === Universe)
  }

  test("union complement") {
    unionComplement(x, y) =?= (-(x union y) === (-x inter -y))
  }

  ignore("intersection complement") {
    intersectComplement(x, y) =?= (-(x inter y) === (-x union -y))
  }

  test("difference self") {
    differenceSelf(x) =?= ((x diff x) === EmptySet)
  }

  test("universe difference") {
    universeDifference(x) =?= ((Universe diff x) === -x)
  }

  ignore("double difference") {
    doubleDifference(x, y) =?= ((x diff (x diff y)) === (x inter y))
  }

  ignore("subset difference") {
    subsetDifference(x, y) =?= ((y sube -x) ->: ((x diff y) === x))
  }

  test("double complement") {
    doubleComplement(x) =?= (-(-x) === x)
  }

  test("universe complement") {
    universeComplement =?= (-Universe === EmptySet)
  }

  ignore("intersection distributivity") {
    intersectDistributivity(x, y, z) =?= ((x inter (y union z)) === ((x inter y) union (x inter z)))
  }

  ignore("union distributivity") {
    unionDistributivity(x, y, z) =?= ((x union (y inter z)) === ((x union y) inter (x union z)))
  }

  test("sum empty") {
    sumEmpty =?= (Sum(EmptySet) === EmptySet)
  }

  test("sum singleton") {
    sumSingleton(x) =?= IsSet(x) ->: (Sum(SingletonSet(x)) === x)
  }

  test("sum singleton empty") {
    sumSingletonEmpty =?= (Sum(SingletonSet(EmptySet)) === EmptySet)
  }

  test("sum universe") {
    sumUniverse =?= (Sum(Universe) === Universe)
  }

  test("power universe") {
    powerUniverse =?= (Power(Universe) === Universe)
  }

  test("subset eq reflexive") {
    subsetEqReflexive(x) =?= (x sube x)
  }

  test("empty subset eq") {
    emptySubsetEq(x) =?= (EmptySet sube x)
  }

  test("subset eq empty") {
    subsetEqEmpty(x) =?= ((x sube EmptySet) <-> (x === EmptySet))
  }

  test("subset eq universe") {
    subsetEqUniverse(x) =?= (x sube Universe)
  }

  test("subset eq transitivity") {
    subsetEqTransitivity(x, y, z) =?= (x sube y) ->: (y sube z) ->: (x sube z)
  }

  test("subset eq inter") {
    subsetEqInter(x, y, z) =?= ((z sube (x inter y)) <-> ((z sube x) /\ (z sube y)))
  }

  test("power monotonicity") {
    powerMonoticity(x) =?= IsSet(x) ->: (x in Power(x))
  }

  test("sum subset eq monotonicity") {
    sumSubsetEqMonotonicity(x, y) =?= (x sube y) ->: (Sum(x) sube Sum(y))
  }

  test("power subset eq monoticity") {
    powerSubsetEqMonoticity(x, y) =?= (x sube y) ->: (Power(x) sube Power(y))
  }

  test("sum power") {
    sumPower(x) =?= IsSet(x) ->: (Sum(Power(x)) === x)
  }

  test("power sum") {
    powerSum(x) =?= (x sube Power(Sum(x)))
  }

  test("power intersect") {
    powerIntersect(x, y) =?= (Power(x inter y) === (Power(x) inter Power(y)))
  }

  test("power empty") {
    powerEmpty =?= (Power(EmptySet) === SingletonSet(EmptySet))
  }

  ignore("power singleton empty") {
    powerSingletonEmpty =?= (Power(SingletonSet(EmptySet)) === PairSet(EmptySet, SingletonSet(EmptySet)))
  }

  test("sum union") {
    sumUnion(x, y) =?= IsSet(x) ->: IsSet(y) ->: (Sum(PairSet(x, y)) === (x union y))
  }

  test("union set") {
    unionSet(x, y) =?= IsSet(x) ->: IsSet(y) ->: IsSet(x union y)
  }

  test("ordered pair set") {
    orderedPairSet(x, y) =?= IsSet(x) ->: IsSet(y) ->: IsSet(OrderedPair(x, y))
  }

  test("product subset eq") {
    productSubsetEq(x, y) =?= (Product(x, y) sube Product(Universe, Universe))
  }

  test("product relation") {
    productRelation(x, y) =?= Relation(Product(x, y))
  }

  test("product contains") {
    productContains(x, y, u, v) =?= IsSet(u) ->: IsSet(v) ->: ((OrderedPair(u, v) in Product(x, y)) <-> ((u in x) /\ (v in y)))
  }

  test("identity relation") {
    identityRelation =?= Relation(Identity)
  }

  test("identity contains") {
    identityContains(x) =?= IsSet(x) ->: (OrderedPair(x, x) in Identity)
  }

  test("identity equals") {
    identityEquals(x, y) =?= IsSet(x) ->: IsSet(y) ->: (OrderedPair(x, y) in Identity) ->: (x === y)
  }

  test("intersect function") {
    intersectFunction(x, y) =?= Fnc(x) ->: Fnc(x inter y)
  }

  test("intersect set") {
    intersectSet(x, y) =?= IsSet(x) ->: IsSet(y inter x)
  }

  test("subset eq set") {
    subsetEqSet(x, y) =?= IsSet(x) ->: (y sube x) ->: IsSet(y)
  }

  test("russell iff") {
    russellIff(x) =?= IsSet(x) ->: ((x in Russell) <-> ~(x in x))
  }

  test("russell class") {
    russellClass =?= ~IsSet(Russell)
  }

  test("universe class") {
    universeClass =?= ~IsSet(Universe)
  }

  test("complement class") {
    complementClass(x) =?= IsSet(x) ->: ~IsSet(-x)
  }
}
