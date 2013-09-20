sealed trait Pred {
  def and(that: Pred): Pred = And(this, that)
  def or(that: Pred): Pred = And(this, that)
  def unary_! = Not(this)
}
object True extends Pred {
  override def and(that: Pred) = that
}
object False extends Pred
sealed trait Comparison extends Pred { def l: Expr; def r: Expr }
case class Eq(l: Expr, r: Expr) extends Comparison
case class GT(l: Expr, r: Expr) extends Comparison
case class LT(l: Expr, r: Expr) extends Comparison
case class GE(l: Expr, r: Expr) extends Comparison
case class LE(l: Expr, r: Expr) extends Comparison
sealed trait BinaryPred extends Pred { def l: Pred; def r: Pred }
case class And(l: Pred, r: Pred) extends BinaryPred
case class Or(l: Pred, r: Pred) extends BinaryPred
case class Not(p: Pred) extends Pred

sealed trait Expr {
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)
  def /(that: Expr) = Div(this, that)
  def ===(that: Expr) = Eq(this, that)
  def <(that: Expr) = LT(this, that)
  def <=(that: Expr) = LE(this, that)
  def >(that: Expr) = GT(this, that)
  def >=(that: Expr) = GE(this, that)
}
case class Var(name: String) extends Expr {
  def apply(exprs: Expr*) = App(this, exprs.toList)
}
case class Const(i: Int) extends Expr
sealed trait BinaryExpr extends Expr { def l: Expr; def r: Expr }
case class Plus(l: Expr, r: Expr) extends BinaryExpr
case class Minus(l: Expr, r: Expr) extends BinaryExpr
case class Times(l: Expr, r: Expr) extends BinaryExpr
case class Div(l: Expr, r: Expr) extends BinaryExpr
case class App(v: Var, args: List[Expr]) extends Expr
object Zero extends Expr
case class Reduce(range: Seq, init: Expr = Zero) extends Expr

// Sequence of values to be reduced
sealed trait Seq
case class Range(l: Expr, h: Expr) extends Seq
case class Compr(expr: Expr, v: Var, r: Seq) extends Seq
case class Join(l: Seq, r: Seq) extends Seq

object Python {
  val prelude = 
"""
class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
    return self[args]
  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result
plus = min
zero = 10000000000000000000000000000
"""
  // translate into python list/generator
  def print(s: Seq): String = s match {
    case Range(l, h) => "range(" + print(l) + ", " + print(h) + ")"
    case Join(l, r) => print(l) + " + " + print(r)
    case Compr(e, v, r) => "[" + print(e) + " for " + print(v) + " in " + print(r) + "]"
  }
  def print(e: Expr): String = e match {
    case Var(n) => n
    case Const(i) => i.toString
    case Plus(l, r) => "(" + print(l) + " + " + print(r) + ")"
    case Minus(l, r) => "(" + print(l) + " - " + print(r) + ")"
    case Times(l, r) => print(l) + "*" + print(r)
    case Div(l, r) => print(l) + "/" + print(r)
    case App(v, args) => print(v) + "(" + args.map(print(_)).mkString(", ") + ")"
    case Reduce(r, init) => "reduce(plus, " + print(r) + ", " + print(init) + ")"
    case Zero => "zero"
  }
  def print(p: Pred): String = p match {
    case True => "True"
    case False => "False"
    case And(l, r) => "(" + print(l) + " and " + print(r) + ")"
    case Or(l, r) => "(" + print(l) + " or " + print(r) + ")"
    case Not(l) => "(not " + print(l) + ")"
    case Eq(l, r) => "(" + print(l) + " == " + print(r) + ")"
    case LT(l, r) => "(" + print(l) + " < " + print(r) + ")"
    case GT(l, r) => "(" + print(l) + " > " + print(r) + ")"
    case LE(l, r) => "(" + print(l) + " <= " + print(r) + ")"
    case GE(l, r) => "(" + print(l) + " >= " + print(r) + ")"
  }
  def print(alg: Alg): String = alg match {
    case Alg(v, dom, cases) => 
      "@memoize def " + print(v) +
      "(" + dom.map(d => print(d.v)).mkString(", ") + "):\n" + 
      dom.collect { case d if d.pred != True  => 
        "  assert " + print(d.pred)
      }.mkString("\n") + 
      "\n" +
      cases.map { case (pred, expr) =>
        "  if " + print(pred) +
        ":\n    return " + print(expr)
      }.mkString("\n")
      
  }
}

object SMT {
  def print(e: Expr): String = (e: @unchecked) match {
    case Var(n) => n
    case Const(i) => i.toString
    case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
    case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
    case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
    case Div(l, r) => "(div " + print(l) + " " + print(r) + ")"
  }
  def print(p: Pred): String = p match {
    case True => "true"
    case False => "false"
    case And(l, r) => "(and " + print(l) + " " + print(r) + ")"
    case Or(l, r) => "(or " + print(l) + " " + print(r) + ")"
    case Not(l) => "(not " + print(l) + ")"
    case Eq(l, r) => "(= " + print(l) + " " + print(r) + ")"
    case LT(l, r) => "(< " + print(l) + " " + print(r) + ")"
    case GT(l, r) => "(> " + print(l) + " " + print(r) + ")"
    case LE(l, r) => "(<= " + print(l) + " " + print(r) + ")"
    case GE(l, r) => "(>= " + print(l) + " " + print(r) + ")"
  }
}

object Collect {
  // Does not consider variable multiplicities
  def vars(e: Expr): Set[Var] = e match {
    case b: BinaryExpr => vars(b.l) ++ vars(b.r)
    case v: Var => Set(v)
    case Const(_) | Zero => Set()
    case App(v, args) => args.map(vars(_)).reduce(_ ++ _) + v
    case Reduce(range, init) => vars(range) ++ vars(init)
  }
  def vars(s: Seq): Set[Var] = s match {
    case _: Range => Set()
    case Join(l, r) => vars(l) ++ vars(r)
    case Compr(expr, v, r) => vars(r) ++ (vars(expr) - v)
  }
  def vars(p: Pred): Set[Var] = p match {
    case b: Comparison => vars(b.l) ++ vars(b.r)
    case b: BinaryPred => vars(b.l) ++ vars(b.r)
    case Not(p) => vars(p)
    case True | False => Set()
  }
}

// Recursive algorithm definition
case class Alg(v: Var, 
  domain: List[Domain], 
  cases: List[(Pred, Expr)]) {
  override def toString = Python.print(this)
  def pre = domain.map(_.pred).reduce(_ and _)
}
// Input table
case class Table(v: Var, dim: Int)

sealed trait Domain {
  def v: Var
  def pred: Pred
}
case class IntDomain(v: Var, r: Range) extends Domain {
  override def pred = r.l <= v and v < r.h
}
case class Any(v: Var) extends Domain {
  override def pred = True
}

object Transform { 
  def transform(p: Pred)(implicit f: PartialFunction[Expr, Expr]): Pred = p match {
    case True => True
    case False => False
    case And(l, r) => And(transform(l), transform(r))
    case Or(l, r) => Or(transform(l), transform(r))
    case Not(l) => Not(transform(l))
    case Eq(l, r) => Eq(transform(l), transform(r))
    case LT(l, r) => LT(transform(l), transform(r))
    case GT(l, r) => GT(transform(l), transform(r))
    case LE(l, r) => LE(transform(l), transform(r))
    case GE(l, r) => GE(transform(l), transform(r))
  }
  def transform(e: Expr)(implicit f: PartialFunction[Expr, Expr]): Expr = 
    if (f.isDefinedAt(e))
      f(e)
    else e match {
      case _: Var => e
      case _: Const => e
      case Plus(l, r) => Plus(transform(l), transform(r))
      case Minus(l, r) => Minus(transform(l), transform(r))
      case Times(l, r) => Times(transform(l), transform(r))
      case Div(l, r) => Div(transform(l), transform(r))
      case App(v: Var, args: List[Expr]) => App(transform(v).asInstanceOf[Var], args.map(transform(_)))
      case Zero => Zero
      case Reduce(range, init) => Reduce(transform(range), transform(init))
    }
  def transform(s: Seq)(implicit f: PartialFunction[Expr, Expr]): Seq = 
    s match {
      case Range(l, h) => Range(transform(l), transform(h))
      case Compr(expr, v, r) => Compr(transform(expr), transform(v).asInstanceOf[Var], transform(r))
      case Join(l, r) => Join(transform(l), transform(r))
    }


  // These transformation are correct by construction
  val z3 = new Z3

  def increment(name: String): String = {
    import java.util.regex._
    val p = Pattern.compile("\\d+$");
    val m = p.matcher(name);
    if (m.find()) {
      val i = m.group();
      name.substring(0, name.size - i.size) + (i.toInt + 1)
    } else
      name + "0"
  }

  def increment(v: Var): Var = Var(increment(v.name))
 
  def pushVars(vs: Var*): Alg => Alg = {
    case Alg(av, dom, cases) =>
      val fresh = increment(av)
      implicit def t: PartialFunction[Expr, Expr] = {
        case App(v, args) if v == av => App(fresh, args ::: vs.toList)
      }
      Alg(fresh, dom ::: vs.toList.map(Any(_)), cases.map { 
          case (pred, expr) => (transform(pred), transform(expr))
      }) 
  }
  
  def split(base: Pred, splits: Map[Var, Expr]): Alg => Alg = {
    case Alg(av, dom, cases) =>
      val fresh = increment(av)

      // create specialized versions of alg by splitting the domain
      var parts: List[(Pred, Expr)] = Nil;
      def rec(vs: List[(Var, Expr)], prefix: Pred = True) {
        vs match {
          case Nil => parts = (prefix, App(av, dom.map(_.v))) :: parts
          case v :: vs => 
            rec(vs, prefix and v._1 < v._2)
            rec(vs, prefix and v._1 >= v._2)
        }        
      }

      rec(splits.toList)
      
      val out = Alg(fresh, dom, 
        (base, App(av, dom.map(_.v))) :: parts.reverse)

      out
  }

  def eliminate: Alg => Alg = {
    case a @ Alg(av, dom, cases) =>
      Alg(increment(av), dom, cases.filter {
          case (pred, _) => z3.solve(a.pre and pred)
      })      
  }

  
}

object Parenthesis {
  implicit def int2expr(i: Int) = Const(i)

  val i = Var("i")
  val j = Var("j")
  val c = Var("c")
  val k = Var("k")
  
  val w = Var("w")
  val x = Var("x")
  val n = Var("n")
  val C = Alg(c, 
    List(
      IntDomain(i, Range(0, n)), 
      IntDomain(j, Range(i+1, n))
    ), 
    List(
      (i === j - 1, x(j)),
      (True, Reduce(Join(
        Compr(c(i, k) + c(k, j), k, Range(i+1, j)),
        Compr(w(i, k, j), k, Range(i+1, j))
      )))
    )
  )


  def main(args: Array[String]) {
    import Console.println
    import Transform._
    println(C)

    val C0 = pushVars(n, w, x)(C)
    println(C0)

    val C1 = split(n < 4, Map(i -> n/2, j -> n/2))(C0)
    println(C1)

    val C2 = eliminate(C1)
    println(C2)

    // now comes the inductive argument:
    // we can substitute c1 by c3 in some cases with appropriate
    // input domain shift

    // need to know: 
    //  order (which is same as dependency graph of the original algorithm)
    //  how to unroll and unify defs
    //  there is a change in induction (induct on n now)
    // prove by (n, i + j)
   
    // claim1: c1(i,j,n) = c1(i,j,n/2) whenever domains overlap
    // proof: induct on i,j; base cases don't have n; n was pushed 


    // claim2: c1(i,j,n/2) = c3(i,j,n/2)
    // proof: induct on n

    Transform.z3.close
  }
}
