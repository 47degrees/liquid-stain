import stainless.lang._
import stainless.collection._
import stainless.annotation._

object chapter3 {

  def zero(x: Int)    = x == 0
  def nonZero(x: Int) = x != 0

  def one = { 1 } ensuring (nonZero(_))
  def badOne = { 1 } ensuring (zero(_))


  /*
  {-@ type Nat   = {v:Int | 0 <= v}        @-}
{-@ type Even  = {v:Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v:Int | v < 100}       @-}
  */

  def nat(x: Int)   = 0 <= x
  def even(x: Int)  = x % 2 == 0
  def lt100(x: Int) = x < 100

  def zeroIsEven  = { 0 } ensuring (even(_))
  def zeroIsLt100 = { 0 } ensuring (lt100(_))

  def die(s: String): Boolean = {
    require(false)
    die(s)
  }

  def cannotDie: Boolean
    = if (1 + 1 == 3) { die("should not be called") } else { true }
  def canDie: Boolean
    = if (1 + 1 == 2) { die("should not be called") } else { true }
}
