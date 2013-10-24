import leon.Utils._

object ListMembers {

  def reverse(list : List[Int]): List[Int] = {
    list match {
      case Nil => Nil
      case head :: Nil => list
      case head :: headone :: tail => reverse(tail) ::: (head :: Nil)
    }
  } ensuring(res => (list.length == res.length))

  def isEmpty(list : List[Int]): Boolean = {
    list match {
      case Nil => true
      case _ => false
    }
  } ensuring(res => (list.length == 0 && res) || (! (list.length == 0) && ! res))

  def nonEmpty(list : List[Int]): Boolean = {
    list match {
      case Nil => false
      case _ => true
    }
  } ensuring(_ == ! isEmpty(list))

  def tail(list : List[Int]): List[Int] = {
    list match {
      case Nil => Nil
      case x :: xs => xs
    }
  }  ensuring( res => res == list.tail)

  def head(list : List[Int]): Int = ({
    require(! isEmpty(list))
    list match {
      case x :: xs => x
    }
  }) ensuring( _ == list.head)

  def drop(list : List[Int], n : Int): List[Int] = {
    list match {
      case x :: xs if(n > 0) => drop(xs, n - 1)
      case x :: xs if(n <= 0) => list
      case Nil => Nil
    }
  } ensuring(res => ((n >= list.length && res == Nil) || (n < list.length && res.length == list.length - n)))

  // Do it the hard way and check against drop
  def dropRight(list : List[Int], n : Int): List[Int] = {
    list match {
      case x :: xs if(list.length > n) => x :: dropRight(xs, n)
      case x :: xs if(n >= list.length)=> Nil
      case Nil => Nil
    }
  } ensuring( _ == reverse(drop(reverse(list), n)))
  //Selects all elements except the last.
  def init(list : List[Int]): List[Int] = {
    list match {
      case x :: Nil => Nil
      case x :: xs => x :: init(list)
      case Nil => Nil
    }
  } ensuring( _ == dropRight(list,1))

  def last(list : List[Int]): Int = ({
    require( ! isEmpty(list))
    list match {
      case x :: Nil => x
      case x :: xs => last(xs)
    }
  })ensuring(_ == head(reverse(list)))

  //Adds the elements of a given list in reverse order in front of this list.
  def reverse_:::(list : List[Int], prefix : List[Int]): List[Int] = {
    reverse(list) ::: prefix
  } ensuring(res => res.length == (list.length+prefix.length) && 
                   drop(res, list.length) == prefix && 
                   reverse(dropRight(res, prefix.length)) == list)

  def slice(list : List[Int], from : Int, until : Int): List[Int] = {
    if(from >= until)
      Nil
    else if(from > list.length)
      Nil
    else if(until <= 0)
      Nil
    else if(from < 0)
      dropRight(list, until)
    else
      list match {
        case Nil => Nil
        case x :: Nil if(from == 0 && until > 0) => list
        case x :: xs if(from > 0 && until > 0 ) => slice(xs, from - 1, until)
        case x :: xs if(from == 0 && until > 0 ) => x :: slice(xs, from, until - 1)
        case x :: xs if(from == 0 && until == 0) => Nil
      }
  } ensuring(res => drop(dropRight(list, list.length-until),from) == res)

  def splitAt(list : List[Int], n : Int): (List[Int], List[Int]) = {

    list match {
      case Nil => (Nil, Nil)
      case x :: xs if(n > 0) => 
        // val (lhs, rhs) = splitAt(xs, n-1)
        // (x :: lhs, rhs)
        splitAt(xs, n-1)
      case x :: xs if(n <= 0) =>
        // val (lhs,rhs) = splitAt(xs, n-1)
        // (lhs, x :: rhs)
        splitAt(xs, n-1)

    }
  }

  def zip(lhs : List[Int], rhs : List[Int]): List[(Int,Int)] = {
    (lhs, rhs) match {
      case (Nil, Nil) => Nil
      case (Nil, _ ) => Nil
      case ( _ , Nil)  => Nil
      case (x :: xs, y :: ys) => (x,y) :: zip(xs,ys)
    }
  } ensuring(res => (lhs.length > rhs.length) && res.length == rhs.length)
}