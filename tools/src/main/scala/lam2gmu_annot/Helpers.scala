package lam2gmu_annot

import scala.annotation.tailrec
import ASTs.ConcreteSyntax._
import ASTs.ConcreteSyntax.Pattern.PatSyntax

object Helpers {
  @tailrec
  def applyFun(fun: Expression, args: Expression*): Expression =
    args match {
      case Seq()                => fun
      case Seq(arg1, rest @ _*) => applyFun(Application(fun, arg1), rest: _*)
    }

  var counter = 0
  def freshLam(): LamVar = {
    counter += 1
    LamVar("_x" + counter)
  }

  def matchConstructor(name: String, typeArgs: Seq[String])(
      builder: LamVar => Expression
  ): Clause = {
    val datavar = freshLam()
    Pattern.ctor(name, typeArgs, datavar.name) -> builder(datavar)
  }
}
