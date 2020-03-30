import stainless.lang._
import stainless.lang.Option._
import stainless.lang.Set._
import stainless.lang.StaticChecks._
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
  def badSP: Sparse[String] = Sparse(5, List((0, "cat"), (6, "dog")))

  def keys[A,B](map: List[(A,B)]): Set[A] = map match {
    case Nil() => Set()
    case (i, _) :: xs => Set(i) ++ keys(xs)
  }

  // This version does not work as good
  // it cannot prove that badSP2 is wrong
  case class Sparse2[A](val spDim: BigInt, val spElems: List[(BigInt, A)]) {
    @invariant
    def indexBounds: Boolean = forall { (x: BigInt) => keys(spElems).contains(x) ==> btwn(0,spDim,x) } 
  }

  def okSP2:  Sparse2[String] = Sparse2(5, List((0, "cat"), (3, "dog")))
  def badSP2: Sparse2[String] = Sparse2(5, List((0, "cat"), (6, "dog")))

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

  // This version does not work
  /*
  def dotProd2(x: List[BigInt], v: Sparse[BigInt]): BigInt = {
    require(x.length > 0 && v.spDim == x.length)

    def body(s: BigInt, e: (BigInt, BigInt)): BigInt = {
      require(btwn(0, v.spDim, e._1))
      s + lookup(x, e._1) * e._2
    }

    v.spElems.foldLeft(BigInt(0))(body)
  } */

  /*
  Hint: You need to check that all the indices in elts are less than dim; the easiest way is to compute a new Maybe [(Int, a)] which is Just the original pairs if they are valid, and Nothing otherwise.

  fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
  fromList dim elts = undefined

  {-@ test1 :: SparseN String 3 @-}
  test1     = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]
  */

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
  } ensuring { _.forall((x: Sparse[A]) => x.spDim == dim && x.indexBounds) }
  // NOTE: without the 'x.indexBounds' the proof does not go through

  def plus(xs: Sparse[BigInt], ys: Sparse[BigInt]): Sparse[BigInt] = {
    require(xs.spDim > 0 && xs.spDim == ys.spDim)

    val dim = xs.spDim

    def findValue(ts: Sparse[BigInt], i: BigInt): BigInt = {
      require(btwn(0, dim, i))

      def go(xs: List[(BigInt, BigInt)]): BigInt = {
        xs match {
          case Nil() => 0
          case (j, v) :: ys => if (j == i) { v } else { go(ys) }
        }
      }

      go(ts.spElems)
    }

    def add(n: BigInt): List[(BigInt, BigInt)] = {
      require(btwn(0, dim+1, n))

      if (n >= dim) {
        Nil[(BigInt, BigInt)]()
      } else {
        Cons((n, findValue(xs, n) + findValue(ys, n)), add(n+1))
      }
    } ensuring { _.forall { (i: (BigInt, BigInt)) => btwn(0, dim, i._1) } } 

    Sparse(dim, add(0))
  }

  /* this kind of implementation does not work
  abstract class OList {
    def contents: Set[BigInt] = this match {
      case ONil => Set()
      case OCons(x, rest) => Set(x) ++ rest.contents
    }
  } 
  case object ONil extends OList
  case class OCons(val x: BigInt, val rest: OList) extends OList {
    @invariant
    def ordered: Boolean = rest.contents.forall { _ >= x }
  } */

  // See https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/verification/valid/BinarySearchTreeQuant.scala

  sealed abstract class Tree {
    def content: Set[BigInt] = this match {
      case Leaf => Set.empty[BigInt]
      case Node(l, v, r) => l.content ++ Set(v) ++ r.content
    }

    def isBST: Boolean = this match {
      case Leaf => true
      case Node(left, v, right) => {
        left.isBST && right.isBST &&
        forall((x:BigInt) => (left.content.contains(x) ==> x < v)) &&
        forall((x:BigInt) => (right.content.contains(x) ==> v < x))
      }
    }
  }
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case object Leaf extends Tree

  def badBST: Tree = {
    Node(Node(Leaf, 4, Leaf), 3, Node(Leaf, 5, Leaf))
  } ensuring { _.isBST }

  sealed abstract class BST2 {
    def min: BigInt = this match {
      case Leaf2(x) => x
      case Node2(l,_,_) => l.min
    }
    def max: BigInt = this match {
      case Leaf2(x) => x
      case Node2(_,_,r) => r.max
    }
  }
  case class Leaf2(x: BigInt) extends BST2
  case class Node2(l: BST2, x: BigInt, r: BST2) extends BST2 {
    @invariant
    def bstOk: Boolean = l.max <= x && x < r.min 
  }

  def badBST2: BST2 = {
    Node2(Node2(Leaf2(2), 4, Leaf2(5)), 3, Leaf2(7))
  }
}