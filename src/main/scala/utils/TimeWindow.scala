package utils

class TimeWindow(val start: Time, val end: Time){
  def duration: Int = Time.duration(start, end)

  def contains(t: Time): Boolean = t >= start && t <= end

  def contains(t: Int): Boolean = contains(Time(t))

  def intersect(w: TimeWindow): Boolean =
    contains(w.start) || contains(w.end) || w.contains(start) || w.contains(end)

  override def toString: String = start + ":" + end
}

object TimeWindow{
  def apply(start: Time, end: Time) = new TimeWindow(start, end)

  def apply(start: Int, end: Int) = new TimeWindow(Time(start), Time(end))

  def apply(s: String) = new TimeWindow(Time(s.split(":")(0)), Time(s.split(":")(1)))

  implicit def timeWindowToInt(w: TimeWindow): Int = w.duration
}
