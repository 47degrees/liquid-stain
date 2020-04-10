import stainless.lang._
import stainless.collection._
import stainless.annotation._

object chapter3 {

  def zero(x: BigInt)    = x == 0
  def nonZero(x: BigInt) = x != 0

  def one = { BigInt(1) } ensuring (nonZero(_))
  def badOne = { BigInt(1) } ensuring (zero(_))


  /*
  {-@ type Nat   = {v:BigInt | 0 <= v}        @-}
  {-@ type Even  = {v:BigInt | v mod 2 == 0 } @-}
  {-@ type Lt100 = {v:BigInt | v < 100}       @-}
  */

  def nat(x: BigInt)   = 0 <= x
  def even(x: BigInt)  = x % 2 == 0
  def lt100(x: BigInt) = x < 100

  def zeroIsEven  = { BigInt(0) } ensuring (even(_))
  def zeroIsLt100 = { BigInt(0) } ensuring (lt100(_))

  def die(s: String): Boolean = {
    require(false)
    die(s)
  }

  def cannotDie: Boolean
    = if (1 + 1 == 3) { die("should not be called") } else { true }
  def canDie: Boolean
    = if (1 + 1 == 2) { die("should not be called") } else { true }

  def dieBigInt(s: String): BigInt = {
    require(false)
    dieBigInt(s)
  }

  def divide(n: BigInt, m: BigInt): BigInt = {
    require(nonZero(m))
    if (m == 0) {
      dieBigInt("divide by zero")
    } else {
      n / m
    }
  }

  def divide2(n: BigInt, m: BigInt): BigInt = {
    require(nonZero(m))
    n / m
  }

  def avg2(x: BigInt, y: BigInt) = divide(x+y, 2)
  def avg3(x: BigInt, y:BigInt, z: BigInt) = divide(x+y+z, 3)
  def avg(ls: List[BigInt]): BigInt = {
    require(ls.size > 0)  // without this we get an error
    divide(ls.foldLeft(BigInt(0))((r, s) => r + s), ls.size)
  }
}
