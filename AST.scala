sealed trait Pred {
  def and(that: Pred): Pred = And(this, that)
  def or(that: Pred): Pred = And(this, that)
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


class Context {
  val values = Map[Var, Map[List[Int], Int]]()
}

object Python {
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
    case Alg(v, args, d, cases) => 
      "@memoize def " + print(v) +
      "(" + args.map(print(_)).mkString(", ") + "):\n" + 
      "  assert " + print(d) + "\n" +
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
  args: List[Var], 
  domain: Pred, 
  cases: List[(Pred, Expr)])
// Input table
case class Table(v: Var, dim: Int)


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

  def pushVars(vs: Var*)(a: Alg, fresh: Var) = a match {
    case Alg(name, args, dom, cases) =>
      implicit def t: PartialFunction[Expr, Expr] = {
        case App(v, args) if v == name => App(fresh, args ::: vs.toList)
      }
      Alg(fresh, args ::: vs.toList, dom, cases.map { 
          case (pred, expr) => (transform(pred), transform(expr))
      }) 
  }

  def partition(base: Pred, ps: Pred*)(a: Alg, fresh: Var) = a match {
    case Alg(name, args, dom, cases) =>
      val rec = App(name, args);
      def preds(ps: List[Pred], out: List[Pred] = True :: Nil): List[Pred] = 
        ps match {
          case Nil => out
          case p :: ps => 
            preds(ps, out.map(_ and p)) :::
            preds(ps, out.map(_ and Not(p)))
        }
      Alg(fresh, args, dom, 
        (base, rec) :: 
        preds(ps.toList).map((_, rec)))               
  }

  val z3 = new Z3

  def elimCases(a: Alg, fresh: Var) =
    Alg(fresh, a.args, a.domain, 
      for ((pred, expr) <- a.cases;
           if z3.solve(pred and a.domain))
           yield (pred, expr))
}

object Parenthesis {
  implicit def string2expr(s: String) = Var(s)
  implicit def int2expr(i: Int) = Const(i)

  val ctx = new Context

  val i = Var("i")
  val j = Var("j")
  val c = Var("c")
  val k = Var("k")
  
  val w = Var("w")
  val x = Var("x")
  val n = Var("n")
  val C = Alg(c, List(i, j), 
    i < n and j < n and i < j and i >= 0 and j >= 0,
    List(
      (i === j - 1, x(j)),
      (True, Reduce(Join(
        Compr(c(i, k) + c(k, j), k, Range(i+1, j)),
        Compr(w(i, k, j), k, Range(i+1, j))
      )))))


  def main(args: Array[String]) {
    Console.out.println(Python.print(C))

    val c1 = Var("c1")
    val C1 = Transform.pushVars(n, w, x)(C, c1)
    Console.out.println(Python.print(C1))

    val c2 = Var("c2")
    val C2 = Transform.partition(n < 4, i < n/2, j < n/2)(C1, c2)
    Console.out.println(Python.print(C2))

    val c3 = Var("c3")
    val C3 = Transform.elimCases(C2, c3)
    Console.out.println(Python.print(C3))

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
