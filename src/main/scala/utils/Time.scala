package utils

class Time(val h: Int, val m: Int) {

  def >(time: Time): Boolean = (60*this.h + this.m) > (60*time.h + time.m)

  def <(time: Time): Boolean = (60*this.h + this.m) < (60*time.h + time.m)

  def ==(time: Time): Boolean = (60*this.h + this.m) == (60*time.h + time.m)

  def >=(time: Time): Boolean = this > time || this == time

  def <=(time: Time): Boolean = this < time || this == time

  def +(time: Time): Time = {

    val newM = (this.m + time.m) % 60

    val newH = (this.h + time.h) + (this.m + time.m) / 60

    new Time(newH,newM)
  }

  def +(i: Int): Time = {
    val newM = (this.toMinutes + i) % 60
    val newH = (this.toMinutes + i) / 60
    new Time(newH,newM)
  }

  def toMinutes: Int = h*60 + m


  override def toString() = {
    val neg = h < 0 || m < 0
    val absh = math.abs(h)
    val absm = math.abs(m)
    (if(neg) "-" else "") + (if(absh < 10) "0" + absh else absh) + "h" + (if(absm < 10) "0" + absm else absm)
  }


}

object Time {

  def duration(startTime: Time, endTime: Time): Int =  endTime.toMinutes - startTime.toMinutes

  def apply(h: Int, m: Int) = new Time(h,m)

  def apply(m: Int): Time = intToTime(m)

  def apply(s: String) = {
    val split = s.split("h")
    val h = split(0).toInt
    val m = if(h < 0) -split(1).toInt else split(1).toInt
    new Time(h, m)
  }

  implicit def timeToInt(t: Time): Int = t.h*60 + t.m

  def intToTime(n: Int): Time = Time(n / 60,n % 60)
}