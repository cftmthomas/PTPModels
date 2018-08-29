package utils

import json.{InstanceGenerator, JsonParser}

object BenchGenerator {

  def main(args: Array[String]) {

    val nSet = 3

    //Debug instances
    val sizeD: Array[(Int, Int, Int)] = Array(
      (1, 1, 1),
      (1, 1, 2),
      (2, 1, 2),
      (2, 2, 2),
      (1, 1, 4),
      (4, 1, 4),
      (4, 2, 4),
      (4, 4, 4)
    )

    //Easy instances
    val sizeE: Array[(Int, Int, Int)] = Array(
      (4, 2, 16),
      (8, 4, 32),
      (12, 5, 48),
      (16, 6, 64),
      (20, 8, 80),
      (24, 9, 96),
      (28, 10, 112),
      (32, 12, 128),
      (36, 14, 144),
      (40, 16, 160)
    )

    //Medium instances
    val sizeM: Array[(Int, Int, Int)] = Array(
      (8, 2, 16),
      (16, 3, 32),
      (24, 4, 48),
      (32, 4, 64),
      (40, 5, 80),
      (48, 5, 96),
      (56, 6, 112),
      (64, 8, 128),
      (72, 8, 144),
      (80, 9, 160)
    )

    //Hard instances
    val sizeH: Array[(Int, Int, Int)] = Array(
      (16, 2, 16),
      (32, 3, 32),
      (48, 4, 48),
      (64, 4, 64),
      (80, 5, 80),
      (96, 5, 96),
      (112, 6, 112),
      (128, 8, 128),
      (144, 8, 144),
      (160, 8, 160)
    )

    for(set <- 1 to nSet){
      for((h, v, p) <- sizeE){
        val generator = new InstanceGenerator(h, v, p)
        val instance = generator.generateInstance("PTP-RAND-" + set + "_" + h + "_" + v + "_" + p)
        JsonParser.writeInstance("data/instances/", instance)
      }
    }
  }
}
