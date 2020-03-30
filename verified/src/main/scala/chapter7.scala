import stainless.lang._
import stainless.lang.Option._
import stainless.lang.Set._
import stainless.lang.StaticChecks._
import stainless.collection._
import stainless.annotation._

object chapter7 {
  /* exists as xs.nonEmpty
  def notEmpty[A](xs: List[A]): Boolean = xs match {
    case Nil() => false
    case _ :: _ => true
  } */

  def myMap[A,B](f: A => B, xs: List[A]): List[B] = {
    xs match {
      case Nil() => Nil[B]()
      case x :: xs => f(x) :: myMap(f,xs)
    }
  } ensuring { _.size == xs.size }

  def myReverse[A](xs: List[A]): List[A] = {
    def go(acc: List[A], ys: List[A]): List[A] = {
      ys match {
        case Nil() => acc
        case y :: ys => go(y :: acc, ys)
      }
    } ensuring { _.size == acc.size + ys.size }

    go(Nil(), xs)
  } ensuring { _.size == xs.size }

  def myTake[A](n: BigInt, xs: List[A]): List[A] = {
    require(n >= 0)
    (n, xs) match {
      case (BigInt(0), _) => Nil[A]()
      case (_, Nil()) => Nil[A]()
      case (i, y :: ys) => y :: myTake(n-1, ys)
    }
  } ensuring { (res: List[A]) => (res.size <= n && res.size <= xs.size) }

  def myPartition[A](f: A => Boolean, xs: List[A]): (List[A], List[A])  = {
    xs match {
      case Nil() => (Nil[A](), Nil[A]())
      case y :: ys => {
        val (yes, no) = myPartition(f, ys)
        if (f(y)) {
          (y :: yes, no)
        } else {
          (yes, y :: no)
        }
      }
    }
  } ensuring { (res: (List[A], List[A])) => res._1.size + res._2.size == xs.size }
}