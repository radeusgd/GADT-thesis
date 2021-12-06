package lam2gmu.testing

import encoding.Encoder
import lam2gmu.{LamParser, Lexer}

import scala.io.StdIn

object TestExpr {
  def main(args: Array[String]): Unit = {
    while (true) {
      val ts = StdIn.readLine("Expr:\n")
      if (ts == null) return
      println(Lexer(ts))
      val ex = LamParser.parseExpr(ts)

      ex match {
        case Left(error) =>
          println(error)
        case Right(expr) =>
          println(expr)
//          val encoder = new Encoder
//          encoder.translateType(typ, Map.empty)
      }
    }
  }
}
