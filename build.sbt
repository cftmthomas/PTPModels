import sbt.librarymanagement.Resolver

name := "patient-transportation-problem"

version := "0.1"

scalaVersion := "2.12.4"

resolvers += Resolver.url("typesafe", url("http://repo.typesafe.com/typesafe/releases/"))

resolvers += "Oscar Snapshots" at "http://artifactory.info.ucl.ac.be/artifactory/libs-snapshot-local/"

libraryDependencies += "com.typesafe.play" %% "play-json" % "2.6.0-M1"

libraryDependencies += "oscar" %% "oscar-cp" % "4.1.0-SNAPSHOT" withSources()
