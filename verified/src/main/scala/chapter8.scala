import stainless.lang._
import stainless.lang.Option._
import stainless.lang.Set._
import stainless.lang.StaticChecks._
import stainless.collection._
import stainless.annotation._

object chapter8 {
  def contents[A](xs: List[A]): Set[A] = xs match {
    case Nil() => Set[A]()
    case x :: xs => Set(x) ++ contents(xs)
  }

  def myAppend[A](xs: List[A], ys: List[A]): List[A] = {
    xs match {
      case Nil()   => ys
      case z :: zs => z :: myAppend(zs, ys)
    }
  } ensuring { contents(_) == contents(xs) ++ contents(ys) }

  def unique(xs: List[BigInt]): Boolean = xs match {
    case Nil()   => true
    case y :: ys => unique(ys) && !ys.contains(y)
  } 

  def okUnique: List[BigInt] = {
    List[BigInt](1, 2, 3)
  } ensuring { unique(_) }

  def badUnique: List[BigInt] = {
    List[BigInt](1, 2, 3, 2)
  } ensuring { unique(_) }
}