import stainless.lang._
import stainless.collection._
import stainless.annotation._

object chapter2 {

  def implies(p: Boolean, q: Boolean) = {
    (p, q) match {
      case (true,  true)  => true
      case (true,  false) => false
      case (false, true)  => true
      case (false, false) => true
    }
  } ensuring (res => res == (!p || q))

}
