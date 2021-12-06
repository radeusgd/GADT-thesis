package lam2gmu.testing

import encoding.Encoder
import lam2gmu.{LamParser, Lexer}

import scala.io.StdIn

object TestType {
   def main(args: Array[String]): Unit = {
      while(true) {
         val ts = StdIn.readLine("Type:\n")
         val res = LamParser.parseType(ts)

         res match {
           case Left(error) =>
             println(error)
           case Right(typ) =>
             println(typ)
             val encoder = new Encoder
             val pdot = encoder.translateType(typ, Map.empty)
             println(pdot)
         }
      }
   }
}
