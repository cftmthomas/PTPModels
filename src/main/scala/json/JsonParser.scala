package json

import java.io.{BufferedWriter, File, FileWriter}

import modelling._
import play.api.libs.json._

import scala.io.Source

object JsonParser{

  //Json implicit converters:
  implicit val placeReads = Json.reads[Place]
  implicit val vehicleReads = Json.reads[Vehicle]
  implicit val patientReads = Json.reads[Patient]
  implicit val ptpinstanceReads = Json.reads[PTPInstance]
  implicit val stepReads = Json.reads[Step]
  implicit val pathReads = Json.reads[Path]
  implicit val solutionReads = Json.reads[Solution]

  implicit val placeWrites = Json.writes[Place]
  implicit val vehicleWrites = Json.writes[Vehicle]
  implicit val patientWrites = Json.writes[Patient]
  implicit val ptpinstanceWrites = Json.writes[PTPInstance]
  implicit val stepWrites = Json.writes[Step]
  implicit val pathWrites = Json.writes[Path]
  implicit val solutionWrites = Json.writes[Solution]

  def readInstance(path: String): PTPInstance = {
    val file: String = Source.fromFile(path).getLines.mkString
    val json: JsValue = Json.parse(file)

    json.as[PTPInstance]
  }

  def writeInstance(filepath: String, instance: PTPInstance): Unit = {
    val json = Json.toJson(instance)

    val path = new File(filepath)
    val out = if(path.isDirectory) new File(path.getAbsolutePath + "/" + instance.name + ".json") else path
    out.createNewFile()
    val writer = new BufferedWriter(new FileWriter(out))
    writer.write(Json.prettyPrint(json))
    writer.close()
  }

  def readSol(path: String): Solution = {
    val file: String = Source.fromFile(path).getLines.mkString
    val json: JsValue = Json.parse(file)

    json.as[Solution]
  }

  def writeSol(filepath: String, sol: Solution): Unit = {
    val json = Json.toJson(sol)

    val out = new File(filepath)
    if(!out.getParentFile.exists()) out.getParentFile.mkdirs()
    out.createNewFile()

    val writer = new BufferedWriter(new FileWriter(out))
    writer.write(Json.prettyPrint(json))
    writer.close()
  }
}