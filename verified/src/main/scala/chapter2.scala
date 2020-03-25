import stainless.lang._
import stainless.collection._
import stainless.annotation._

object chapter2 {

  def ==>(p: Boolean, q: Boolean) = {
    (p, q) match {
      case (true,  true)  => true
      case (true,  false) => false
      case (false, true)  => true
      case (false, false) => true
    }
  } ensuring (res => res == (!p || q))

  // holds is equivalent to ensuring { (res: Boolean) => res }
  def ex0a: Boolean = { true } holds
  def ex0b: Boolean = { false } holds

  def ex1(p: Boolean) = { p || !p } holds
  def ex2(p: Boolean) = { p && !p } holds

  def ex3(p: Boolean, q: Boolean) = { (p && q) ==> p } holds
  def ex4(p: Boolean, q: Boolean) = { (p && q) ==> q } holds

  def ax0a: Boolean = { 1 + 1 == 2 } holds
  def ax0b: Boolean = { 1 + 1 == 3 } holds

  // If we use Int, overflow is taken into account!
  def ax1(x: BigInt) = { x < x + 1 } holds
  def ax2(x: BigInt) = { x < 0 ==> 0 <= 0 - x } holds
  def ax3(x: BigInt, y: BigInt)
    = { 0 <= x ==> (0 <= y ==> 0 <= x + y) } holds
  def ax4(x: BigInt, y: BigInt)
    = { x == y - 1 ==> (x + 2 == y + 1) } holds
  def ax5(x: BigInt, y: BigInt, z: BigInt)
    = { (x <= 0 && x >= 0) ==> ( (y == x + z) ==> (y == z)) } holds

  def congruence(f: BigInt => BigInt, x: BigInt, y: BigInt)
    = { (x == y) ==> (f(x) == f(y)) } holds
  def fx1(f: BigInt => BigInt, x: BigInt)
    = { (x == f(f(f(x)))) ==> ( (x == f(f(f(f(f(x)))))) ==> (x == f(x)) ) } holds
}
