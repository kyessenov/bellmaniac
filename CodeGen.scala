// Turn functions into NumPy tables
// Use user-provided looping construct
// Treat first 'dom' arguments as indexes into tables
class NumPython(val dom: Int, val loop: String) extends PythonPrinter {
  assert (dom > 0)
  val T = Var("T", dom)
  def prelude = """plus = min
zero = pow(10, 20)
DIM = 32
MIN = 0
MAX = 1000
from numpy import *
""" + "T = zeros((" + (1 to dom).map(_ => "DIM").mkString(", ") + "), int)\n"

  var scope: Option[Algorithm] = None
  override def print(e: Expr) = e match {
    case App(v, args) => 
      if (algorithms.exists(_.v == v)) 
        scope match {
          case Some(a) if a.v == v && args.drop(dom) == a.args.drop(dom) =>      
            "T[" + print(args.take(dom)) + "]"
          case _ =>
            "??? " + print(v)
        }
      else
        print(v) + "[" + print(args) + "]"
    case _ => super.print(e)
  }

  def print(l: List[Expr]): String = l.map(print(_)).mkString(", ")
  
  def indent = (1 to dom).map(_ => "  ").mkString("")

  override def print(c: Computation) = c match {
    case Input(v) =>
      print(v) + " = " + {
        if (v.arity == 0) 
          "DIM" 
        else 
          "random.randint(MIN, MAX, size=(" + 
          (1 to v.arity).map(_ => "DIM").mkString(", ") + "))"
      }
    case a @ Algorithm(v, args, pre, e) =>        
      scope = Some(a)
      "def " + print(v) + "(" + print(T :: args.drop(dom)) + "):\n" +
      loop + "\n" +
      "  " + indent + "assert " + print(pre) + "\n" +   
      "  " + indent + "T[" + print(args.take(dom)) +"] = " + print(e)
  }
 
  // capture all programs
  var all: List[Computation] = _ 
  override def print(p: List[Computation], out: java.io.PrintStream) {
    all = p
    super.print(p, out)
  }
  def inputs = all.collect { case i: Input => i }
  def algorithms = all.collect { case a: Algorithm => a }
}

