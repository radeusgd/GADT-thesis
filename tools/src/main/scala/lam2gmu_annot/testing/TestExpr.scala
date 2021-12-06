package lam2gmu_annot.testing

import encoding.Encoder
import lam2gmu_annot.{LamParser, Lexer}

import scala.io.StdIn

object TestExpr {
  def main(args: Array[String]): Unit = {
    while (true) {
      val ts = StdIn.readLine("Expr:\n")
      if (ts == null || ts == "") return
      println(Lexer(ts))
      val ex = LamParser.parseExpr(ts)

      ex match {
        case Left(error) =>
          println(error)
        case Right(expr) =>
          println(expr)
          val encoder = new Encoder
          val pdot = encoder.translateExpr(expr)
          println(pdot)
      }
    }
  }
}
