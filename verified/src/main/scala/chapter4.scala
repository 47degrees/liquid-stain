import stainless.annotation._
import stainless.lang.Option
import stainless.lang.None
import stainless.lang.Some

object chapter4 {


  // Array bounds verification
  // This is already built into Stainless, the following example fails
  //TODO uncomment this for push
  def testArrayIndexing = Array(1,2,3,4)(10)


  //Example where we look at how to verify safe indexing of an external vector library

  // When a function is annotated with @extern, Stainless will not attempt to extract
  // the method's body .

  // When a function is annotated with @pure, Stainless will treat a function as pure
  // Stainless assumes by default that extern functions and methods mutate their arguments.

  // When functions or class methods are annotated with @library, Stainless will not
  // verify them.

  @library
  object externalVectorLib {

    sealed trait Vec[A]
    case class Nill[A]() extends Vec[A]
    case class Conz[A](a: A, v: Vec[A]) extends Vec[A]

    def isize[A](l: Vec[A]): BigInt = (l match {
      case Nill() => 0
      case Conz(x, rest) => 1 + isize(rest)
    })

    // mock the behavior of an index based lookup
    def ilookup[A](i: BigInt, v: Vec[A]): A = {
      v match {
        case Nill() => mkException[A]
        case Conz(x, xs) => if (i == 0) x else ilookup(i - 1, xs)
      }
    }

    @extern
    def mkException[A]: A = throw new Exception("out of bounds")
  }

  // Pretend the above is defined in some module we have access to,
  // but we don't get to modify the source code.

  object OurCode {

    import chapter4.externalVectorLib._

    // our safe wrapper type
    case class SafeVec[A](@extern vec: Vec[A]) {

      // Now we make some assumptions about Vec

      // size will always be at least zero
      @extern @pure
      def size[A]: BigInt = {
        isize(vec)
      } ensuring {
        res => res >=0
      }

      // index should be within 0 and the length of the vector
      @extern @pure
      def lookup(i: BigInt): A = {
        require(i >= 0 && i < this.size)
        ilookup(i,vec)
      }
    }

    // adding an implicit conversion from Vec to SafeVec
    implicit def convert[A](v: Vec[A]): SafeVec[A] = SafeVec(v)

    // Verification: Vector Lookup

    // This fails and finds a counter example!
    // When v = Nill our size is 0 and fails the lookup precondition where i < size or 0 < 0
    def head[A](v: Vec[A]): A = v.lookup(0)

    // This is valid! We restrict the function to non empty vectors.
    def head_nonEmpty[A](v: Vec[A]): A = {
      require(v.size > 0)
      v.lookup(0)
    }

    // Exercise: (Vector Head): Write a function that accepts all vectors
    // but returns a value only when the input vector is not empty
    def head_option[A](v: Vec[A]): Option[A] =
      if (v.size > 0) Some(head_nonEmpty(v)) else None[A]

    // Exercise: (Unsafe Lookup):
    // If we take the index first the vector must be at least as long as the index
    // the index should still be greater than 0
    def unsafeLookup[A](i: BigInt)(v: Vec[A]): A = {
      require(v.size > 0 && i >= 0 && i < v.size)
      v.lookup(i)
    }

    // Exercise: (Safe Lookup): write a function safeLookup that checks the bounds
    // before performing the access.
    def validIndex(i: BigInt, vlen: BigInt): Boolean =
      (vlen > 0 && i >=0 && i < vlen)

    def safeLookup[A](v: Vec[A], i: BigInt): Option[A] = {
      if(validIndex(i,v.size)) Some(v.lookup(i)) else None[A]
    }
  }
}