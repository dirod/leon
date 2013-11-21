import leon.Utils._

object FLS {
//   def tail(f : List[Int]): List[Int] ={ 
//     f match {
//       case x :: xs => xs
//       case x :: Nil => Nil
//       case Nil => Nil
//     }
//   }ensuring(res => isSubList(res, f))

  // def isEmpty(f : List[Int]): Boolean = {
  //   f match {
  //     case x :: y  => false
  //     case Nil => true
  //   }
  // }ensuring( res => res == (f.length == 0)) 
	def drop(n: Int, xs: List[Int]): List[Int] = {
		if(n <= 0) xs
		else xs match {
      case Nil => Nil
      case x :: ys => drop(n-1, ys)
    } 
	} ensuring (zs => ( (!(n < 0)) || zs == xs) &&
                    ((!(n >= 0 && xs.length < n)) || zs == Nil) &&
                    (( (!(n >= 0 && xs.length >= n)) || isSubList(zs,xs)) && (zs.length == xs.length - n)))

  // def gcsredef(xs: List[Int], lxs: Int, ys: List[Int], lys: Int): (List[Int], Int) = {
  //   require(xs.length == lxs && ys.length == lys)
  //   (xs,ys) match {
  //     case (Nil, _ ) => (Nil, 0)
  //     case ( _, Nil) => (Nil, 0)
  //     case (x :: x1s, y :: y1s) =>
  //       if(lxs > lys) gcsredef(x1s, lxs-1, ys, lys)
  //       else if(lxs < lys) gcsredef(xs, lxs, y1s, lys-1)
  //       else {
  //         val (z1s, lz1s) = gcsredef(x1s, lxs-1, y1s, lys-1)
  //         if(x == y && lz1s == (lxs - 1)) (x :: z1s, lz1s+1) else (z1s, lz1s)
  //       }
  //   }
  //   //Can't find type if (zs, lzs) => ...
  // } ensuring(p => (p._1.length == p._2 && p._1 == gcs(xs,ys)))

}