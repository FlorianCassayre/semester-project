import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._
import theory.NBGTheory._
import theory.NBGRules._
import theory.NBGTheorems._
import theory.number.NumberTheory._
import theory.number.NumberRules._
import theory.number.NumberTheorems._

object Main extends App {

  val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])
  val tpq = oops(p <-> q)
  val tp = oops(p)
  val tq = oops(q)

  val (x, y, z) = (SetVariable("x"), SetVariable("y"), SetVariable("z"))
  val id = "id"

}
