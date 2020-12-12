package lam2gu.testing

import lam2gu.{LamParser, Lexer}

import scala.io.StdIn

object TestExpr {
  def main(args: Array[String]): Unit = {
    while (true) {
      val ts = StdIn.readLine("Expr:\n")
      if (ts == null) return
      println(Lexer(ts))
      val ex = LamParser.parseExpr(ts)
      println(ex)
    }
  }
}
