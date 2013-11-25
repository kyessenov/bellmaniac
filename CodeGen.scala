// Turn functions into NumPy tables
// Use user-provided looping construct
// Treat first 'dom' arguments as indexes into tables
class NumPython(val dom: Int) extends PythonPrinter {
  assert (dom > 0)
  val T = Var("T", dom)
  def prelude = """plus = min
zero = pow(10, 20)
DIM = 32
MIN = 0
MAX = 1000
from numpy import *
""" + "T = zeros((" + (1 to dom).map(_ => "DIM").mkString(", ") + "), int)"

  var scope: Option[Algorithm] = None
  override def print(e: Expr) = e match {
    case a @ App(v, args) => 
      if (algorithms.exists(_.v == v)) 
        scope match {
          case Some(a) if a.v == v && args.drop(dom) == a.args.drop(dom) =>      
            "T[" + print(args.take(dom)) + "]"
          case _ =>
            a.toString
        }
      else if (inputs.exists(_.v == v) || 
               (scope.isDefined && scope.get.args.exists(_ == v))) 
        print(v) + "[" + print(args) + "]"
      else { 
        error("unknown var: " + v)
        ???
      }
    case _ => super.print(e)
  }

  def print(l: List[Expr]): String = l.map(print(_)).mkString(", ")
  
  def indent(tabs: Int = dom+1) = (1 to tabs).map(_ => "  ").mkString("")

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
      val (lvars, lbounds, lmap) = new LoopConstruct(a, dom).generate

      "def " + print(v) + "(" + print(T :: args.drop(dom)) + "):\n" +
      (for (((lv, Range(l, h)), i) <- lvars zip lbounds zipWithIndex) yield indent(i+1)+
        "for "+print(lv)+" in xrange("+print(l)+","+print(h)+"):\n").mkString("") + 
      (for ((l,i) <- lmap zipWithIndex) yield indent()+
        args(i)+" = "+lmap(i)+"\n").mkString("")+
      indent() + "assert " + print(pre) + "\n" +   
      indent() + "T[" + print(args.take(dom)) +"] = " + print(e)
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


// Generate loop construct for an algorithm
// Additional references:
//    polyhedral model on wiki
//    Omega library tutorials (e.g. SUIF)

case class Rotation(flips: List[Boolean]) {  
  def apply(a: List[Expr]) = a zip flips map { 
    case (x, false) => x
    case (x, true) => Const(0) - x
  }
  def inverse = this
}
object Rotation {
  def all(d: Int): Iterator[Rotation] =   
    if (d == 0)
      List(Rotation(Nil)).iterator
    else
      (all(d-1) map { case Rotation(flips) => Rotation(false :: flips) }) ++
      (all(d-1) map { case Rotation(flips) => Rotation(true :: flips) })
}

case class Vector(path: Pred, c: List[Expr])

class LoopConstruct(a: Algorithm, dim: Int) extends Logger {
  assert (dim > 0)
  import Transform._

  val pre = a.pre
  val c = a.args.take(dim)
  
  // find all recursion references
  def vectors = {
    var out: List[Vector] = Nil
    visit(a.expr)(a.pre, exprTransformer {
      // TODO should check for all variables, not just "a"
      case (path, App(v, vargs)) if v == a.v =>
        out = Vector(path, vargs.take(dim)) :: out
        Havoc
    })
    out
  }

  // domination order
  def LE(a: List[Expr], b: List[Expr]) = 
    a zip b map { case (x, y) => x <= y} reduce(And)
  
  // find domination order orientation
  def orient(vs: List[Vector]): Rotation = {
    for (r <- Rotation.all(dim))
      if (vs.forall { case Vector(p, v) => SMT.prove(p implies LE(r(v), r(c))) })
        return r
    error("can't orient in domination order")
    ???
  }
  implicit def int2rat(n: Int) = new Rational(n, 1)
  implicit def int2expr(n: Int) = Const(n)
  implicit def int2linear(n: Int) = Linear.make(Map(), new Rational(n, 1))

  // solve for max expression
  def MAX(p: List[Expr], pred: Pred): Expr = p match {
    case Nil => ???
    case e :: Nil => e
    case e :: p1 =>
      val e1 = MAX(p1, pred)
      if (SMT.prove(pred implies e1 <= e))
        e
      else if (SMT.prove(pred implies e <= e1))
        e1
      else {
        error("can't find max of " + p)
        ???
      }
  }
  def MIN(p: List[Expr], pred: Pred): Expr = p match {
    case Nil => ???
    case e :: Nil => e
    case e :: p1 =>
      val e1 = MIN(p1, pred)
      if (SMT.prove(pred implies e <= e1))
        e
      else if (SMT.prove(pred implies e1 <= e))
        e1
      else {
        error("can't find min of " + p)
        ???
      }
  }

  // generate looping construct for first "dim" parameters of "a"
  // returns (list of iteration variables, list of their ranges, assignment to actual variables)
  def generate: (List[Var], List[Range], List[Expr]) = {
    // orient dependency vectors by flipping +/- coordinates so that they point
    // into lower-left corner
    val r = orient(vectors)

    // find iteration order and bounds
    // create fresh variables: c1 = r(c)
    val c1 = c.map(_.fresh)
    
    // formulate pre in terms of c1
    val exprs = r.inverse(c1)
    val pre1 = pre.s(c zip exprs)
    
    // free variables
    val freev = Vars(pre1) -- c1

    // get constraints
    val eqs = Linear.equations(pre1)

    def inferBounds(p: List[Var]): Option[List[Range]] = {
      var done = freev
      var out: List[Range] = Nil
      for (v <- p) {        
        done = done + v
        // find constraints only contains "done" vars and having "v"
        val bounds = eqs.filter { case eq => eq.has(v) && eq.vars.subsetOf(done) }
      
        // upper and lower bound expressions
        val lower = bounds.filter(_.proj(v) > 0).map { 
          case eq => 0 - (eq.drop(v) / eq.proj(v)) }.map(_.expr)
        val upper = bounds.filter(_.proj(v) < 0).map { 
          case eq => 1 - (eq.drop(v) / eq.proj(v)) }.map(_.expr)

        if (lower.size == 0 || upper.size == 0)
          return None

        out = Range(MAX(lower, pre1), MIN(upper, pre1)) :: out
      }

      return Some(out.reverse)
    }

    // try to order variables so that we can solve them one by one
    for (p <- c1.permutations) 
      inferBounds(p) match {
        case Some(ranges) => return (p, ranges, exprs)
        case _ =>
      }
   
    println(pre1)
    println(eqs)
    ???
  }
}
