import stainless.lang._
import stainless.collection._
import stainless.annotation._

object chapter5 {
  def nat(x: BigInt) = 0 <= x
  def btwn(l: BigInt, h: BigInt, x: BigInt) = l <= x && x < h

  case class Sparse[A](val spDim: BigInt, val spElems: List[(BigInt, A)]) {
    @invariant
    def dimIsNat: Boolean = spDim > 0
    @invariant
    def indexBounds: Boolean = spElems.forall { (i: (BigInt, A)) => btwn(0,spDim,i._1) }
  }

  def okSP:  Sparse[String] = Sparse(5, List((0, "cat"), (3, "dog")))
  def basSP: Sparse[String] = Sparse(5, List((0, "cat"), (6, "dog")))

  /*
  {-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
  dotProd x (SP _ y) = go 0 y
    where
      go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
      go sum []            = s
  */

  def lookup[A](xs: List[A], n: BigInt): A = {
    require(xs.size > 0 && btwn(0, xs.size, n))
    (n, xs) match {
      case (BigInt(0), y :: ys) => y
      case (_, y :: ys) => lookup(ys, n-1)
    }
  }

  def dotProd(x: List[BigInt], v: Sparse[BigInt]): BigInt = {
    require(x.length > 0 && v.spDim == x.length)

    def go(s: BigInt, w: List[(BigInt, BigInt)]): BigInt = {
      // I had to add this to make the program compile
      require(w.forall { _ match { case (i, _) => btwn(0,v.spDim,i)} })
      w match {
        case Cons((i, v), ys) => go(s + lookup(x, i) * v, ys)
        case Nil() => s
      }
    }

    go(0, v.spElems)
  }

  def dotProd2(x: List[BigInt], v: Sparse[BigInt]): BigInt = {
    require(x.length > 0 && v.spDim == x.length)

    def body(s: BigInt, e: (BigInt, BigInt)): BigInt = {
      require(btwn(0, v.spDim, e._1))
      s + lookup(x, e._1) * e._2
    }

    v.spElems.foldLeft(BigInt(0))(body)
  }

  /*
  Hint: You need to check that all the indices in elts are less than dim; the easiest way is to compute a new Maybe [(Int, a)] which is Just the original pairs if they are valid, and Nothing otherwise.

  fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
  fromList dim elts = undefined

  {-@ test1 :: SparseN String 3 @-}
  test1     = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]
  */

  def noneOrSatisfies[A](p: A => Boolean)(x: Option[A]): Boolean = x match {
    case None()  => true
    case Some(x) => p(x)
  }

  def fromList[A](dim: BigInt, elems: List[(BigInt, A)]): Option[Sparse[A]] = {
    elems match {
      case Nil() => Some(Sparse(dim, List[(BigInt, A)]()))
      case (i, v) :: ys => {
        if (btwn(0, dim, i)) {
          fromList(dim, ys) match {
            case Some(Sparse(d, elems)) => Some(Sparse(d, (i, v) :: elems))
            case None() => None[Sparse[A]]()
          }
        } else {
          None[Sparse[A]]()
        }
      }
    }
  } ensuring { noneOrSatisfies[Sparse[A]](_.spDim == dim)(_) }

  def plus(xs: Sparse[BigInt], ys: Sparse[BigInt]): Sparse[BigInt] = {
    require(xs.spDim == ys.spDim)

    val dim = xs.spDim

    def findValue(ts: Sparse[BigInt], i: BigInt): BigInt = {
      require(btwn(0, ts.spDim, i))

      def go(xs: List[(BigInt, BigInt)]): BigInt = {
        xs match {
          case Nil() => 0
          case (j, v) :: ys => if (j == i) { v } else { go(ys) }
        }
      }

      go(ts.spElems)
    }

    def add(n: BigInt): List[(BigInt, BigInt)] = {
      if (n >= dim) {
        Nil[(BigInt, BigInt)]()
      } else {
        Cons((n, findValue(xs, n) + findValue(ys, n)), add(n+1))
      }
    } ensuring { _.forall { (i: (BigInt, BigInt)) => btwn(0, dim, i._1) } } 

    Sparse(dim, add(0))
  }
}