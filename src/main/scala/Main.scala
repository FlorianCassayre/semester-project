import theory.NBGTheorems

object Main extends App with NBGTheorems {

  val (p, q, r) = (Variable("p"), Variable("q"), Variable("r"))
  val tpq = oops(p <-> q)
  val tp = oops(p)
  val tq = oops(q)

  val (x, y, z) = (SetVariable("x"), SetVariable("y"), SetVariable("z"))
  val id = "id"

}
