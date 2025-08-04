ThisBuild / scalaVersion := "3.3.1"

lazy val root = (project in file("."))
  .settings(
    name := "LazyLambdaMu",
    version := "0.1.0",
    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "2.3.0",
      "org.scalatest" %% "scalatest" % "3.2.18" % Test   
    )
  )

