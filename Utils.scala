trait Logger {
  // throw on exception on error
  var STRICT = true

  // print an important message
  def message(s: => String) = {
    print(Console.RED)
    println(s)
    print(Console.RESET)
  }

  // print an error
  def error(s: => String) = 
    if (STRICT)
      throw new RuntimeException(s)
    else {
      val elts = Thread.currentThread().getStackTrace()
      var caller = elts(3)
      message("*** Error occurred in " + caller.getMethodName + " at " + caller.getLineNumber)
      message(s)
    }
  
  def print(s: => Any) = Console.out.print(s.toString)
  def println(s: => Any) = Console.out.println(s.toString)
}
