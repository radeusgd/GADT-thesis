package lam2gmu.testing

import lam2gmu.LamParser

import scala.io.StdIn

object TestType {
   def main(args: Array[String]): Unit = {
      while(true) {
         val ts = StdIn.readLine("Type:\n")
         if (ts == null || ts == "") {
           return
         }
         val res = LamParser.parseType(ts)

         res match {
           case Left(error) =>
             println(error)
           case Right(typ) =>
             println(typ)
         }
      }
   }
}
