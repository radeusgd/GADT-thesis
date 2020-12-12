name := "LambdaGADT"

version := "0.1"

scalaVersion := "2.12.7"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"

//libraryDependencies += "org.tpolecat" %% "atto-core"    % "0.7.0"
//libraryDependencies += "org.tpolecat" %% "atto-refined" % "0.7.0"
//libraryDependencies += "org.parboiled" %% "parboiled" % "2.1.8"

resolvers += "bintray-djspiewak-maven" at "https://dl.bintray.com/djspiewak/maven"

val ParsebackVersion = "0.3"

//libraryDependencies += "com.codecommit" %% "parseback-core" % ParsebackVersion
//libraryDependencies += "com.codecommit" %% "parseback-cats" % ParsebackVersion