package lam2gu.testing

import lam2gu.{LamParser, Lexer}

import scala.io.StdIn

object TestType {
   def main(args: Array[String]): Unit = {
      while(true) {
         val ts = StdIn.readLine("Type:\n")
         val typ = LamParser.parseType(ts)
         println(typ)
      }
   }
}
