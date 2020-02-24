package theory.fol

trait FOL {

  type Id = String

  type Theory

  trait Named {
    val id: Id
  }

  abstract class Formula {
    private def checkExclusive(a: Set[Named], b: Set[Named]): Unit =
      assert(a.forall(e => b.filter(_.id == e.id).forall(_ == e)))

    this match {
      case Implies(x, y) => checkExclusive(x.ids, y.ids)
      case Iff(x, y) => checkExclusive(x.ids, y.ids)
      case Or(x, y) => checkExclusive(x.ids, y.ids)
      case And(x, y) => checkExclusive(x.ids, y.ids)
      case Forall(named, formula) => checkExclusive(Set(named), formula.ids)
      case Exists(named, formula) => checkExclusive(Set(named), formula.ids)
      case Equals(a, b) => ???
      case _ =>
    }

    def ids: Set[Named] = this match {
      case v@Variable(id) => Set(v)
      case Implies(x, y) => x.ids ++ y.ids
      case Not(x) => x.ids
      case Iff(x, y) => x.ids ++ y.ids
      case Or(x, y) => x.ids ++ y.ids
      case And(x, y) => x.ids ++ y.ids
      case Forall(named, f) => f.ids + named
      case Exists(named, f) => f.ids + named
      case False | True => Set.empty
      case Equals(a, b) => ???
    }
  }
  case class Variable(id: Id) extends Formula with Named
  case class Implies(x: Formula, y: Formula) extends Formula
  case class Not(x: Formula) extends Formula
  case class Iff(x: Formula, y: Formula) extends Formula
  case class Or(x: Formula, y: Formula) extends Formula
  case class And(x: Formula, y: Formula) extends Formula
  case class Forall(named: Named, formula: Formula) extends Formula
  case class Exists(named: Named, formula: Formula) extends Formula
  case object False extends Formula
  case object True extends Formula
  case class Equals(a: Theory, b: Theory) extends Formula

  final class Theorem private(val formula: Formula) { }
  object Theorem {
    private[fol] def apply(formula: Formula): Theorem = new Theorem(formula)
  }

}
