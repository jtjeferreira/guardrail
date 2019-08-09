package support

import examples.server.play.Implicits
import play.api.libs.json._

class PositiveLong private (val value: Long) extends AnyVal
object PositiveLong {
  def apply(value: Long): Option[PositiveLong] = if (value >= 0) Some(new PositiveLong(value)) else None
  implicit val showable                        = Implicits.Show.build[PositiveLong](_.value.toString())
  implicit val decodePositiveLong              = Reads.filterNot[Long](JsonValidationError("error.min"))(_ > 0)
}
