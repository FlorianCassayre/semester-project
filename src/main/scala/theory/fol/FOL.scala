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
      case Equals(a, b) =>  // ??? // TODO
        // TODO membership
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
      case Equals(a, b) => Set.empty // ??? // TODO
      case _ => Set.empty // ??? // TODO
    }

    def ->:(that: Formula): Formula = Implies(that, this)
    def <->(that: Formula): Formula = Iff(this, that)
    def /\(that: Formula): Formula = And(this, that)
    def \/(that: Formula): Formula = Or(this, that)
    def unary_~ : Formula = Not(this)
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

  final class Theorem private(val formula: Formula) {
    def apply(p: Theorem): Theorem = generalModusPonens(this, p) // Modus ponens shorthand
    override def toString: String = formula.toString
  }
  object Theorem {
    private[theory] def apply(formula: Formula): Theorem = new Theorem(formula)
  }

  /** `q` given `p [<]-> q` and `p` */
  def generalModusPonens(pq: Theorem, p: Theorem): Theorem

  private var i: Int = 0
  def fresh(): String = {
    val id = i
    i += 1
    "$" + id
  }

}
