object Nested5 {

  def foo(a: Int): Int = {
    require(a >= 0)
    def bar(b: Int): Int = {
      require(b > 0)
      b + 3
    } ensuring(prop(a, b) && a >= 0 && _ == b + 3)
    bar(2)
  } ensuring(a >= 0 && _ == 5)

  def prop(x: Int, y: Int): Boolean = x + y > 0

}
