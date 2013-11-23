sealed trait Computation {
  def v: Var
}

// Recursive algorithm definition
case class Algorithm(v: Var, args: List[Var], pre: Pred, expr: Expr) extends Computation {
  assert (v.arity == args.size)
  override def toString = Python.print(this)
  // Extend to application of that by supplying remaining arguments 
  def lift(that: Funct)(rest: Expr*) = {
    val args1 = args.map(_.fresh)
    OpVar(that, args1, args1 ++ rest.toList)
  }
  // Generalize to a smaller argument list
  def capture(k: Int) = {
    val args1 = args.take(k).map(_.fresh)
    OpVar(v, args1, args1 ::: args.drop(k))
  }
  // Generalize and translate simultaneously
  def gen(k: Int)(exprs: Expr*) = {
    val args1 = args.take(k).map(_.fresh)
    OpVar(v, args1, exprs.toList.map(_.s(args.take(k) zip args1)))
  }

  def translate(op: (Var, Expr)*) = 
    v.translate(args, op: _*)
}

// Input table (v arguments are one-dimensional)
case class Input(v: Var) extends Computation {
  override def toString = Python.print(this)
}

sealed trait Term 

// Boolean predicate
sealed trait Pred extends Term {
  def and(that: Pred): Pred = (this, that) match {
    case (p, True) => p
    case (True, p) => p
    case _ => And(this, that)
  }
  def or(that: Pred): Pred = (this, that) match {
    case (p, False) => p
    case (False, p) => p
    case _ => Or(this, that)
  }
  def implies(that: Pred): Pred = (! this) or that
  def unary_! = Not(this)  
  override def toString = Python.print(this)
  def s(subs: List[(Var, Expr)]) = 
    Transform.substitute(this, subs.toMap)
}
object True extends Pred 
object False extends Pred 
sealed trait Comparison extends Pred { 
  def l: Expr
  def r: Expr 
}
case class Eq(l: Expr, r: Expr) extends Comparison
case class GT(l: Expr, r: Expr) extends Comparison
case class LT(l: Expr, r: Expr) extends Comparison
case class GE(l: Expr, r: Expr) extends Comparison
case class LE(l: Expr, r: Expr) extends Comparison
sealed trait BinaryPred extends Pred { 
  def l: Pred
  def r: Pred 
}
case class And(l: Pred, r: Pred) extends BinaryPred
case class Or(l: Pred, r: Pred) extends BinaryPred
case class Not(p: Pred) extends Pred

// Expression language
sealed trait Expr extends Term {
  def +(that: Expr) = (this, that) match {
    case (Const(0), e) => e
    case (e, Const(0)) => e
    case _ => Plus(this, that)
  }
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = (this, that) match {
    case (Const(0), e) => Const(0)
    case (Const(1), e) => e
    case (e, Const(0)) => Const(0)
    case (e, Const(1)) => e
    case _ => Times(this, that) 
  }
  def /(that: Expr) = Div(this, that)
  def mod(that: Expr) = Mod(this, that)
  def ===(that: Expr) = Eq(this, that)
  def <(that: Expr) = LT(this, that)
  def <=(that: Expr) = LE(this, that)
  def >(that: Expr) = GT(this, that)
  def >=(that: Expr) = GE(this, that)
  override def toString = Python.print(this)
  def arity = 0
  def where(v: Var) = {
    val that = this
    new { def in(r: Range) = Compr(that, v, r) }
  }
  def s(subs: List[(Var, Expr)]) = Transform.substitute(this, subs.toMap)
}

// Fall through conditional statement
case class Cond(cases: List[(Pred, Expr)], default: Expr = Havoc) extends Expr {
  def ELIF(pe: (Pred, Expr)) = Cond(cases :+ pe, default)
  def ELSE(e: Expr) = Cond(cases, e)
}
object IF {
  def apply(pe: (Pred, Expr)) = Cond(pe :: Nil)
}

// Algebra on integers 
case class Const(i: Int) extends Expr 
object Havoc extends Expr
sealed trait BinaryExpr extends Expr { 
  assert (l.arity == 0 && r.arity == 0)
  def l: Expr
  def r: Expr 
}
case class Plus(l: Expr, r: Expr) extends BinaryExpr
case class Minus(l: Expr, r: Expr) extends BinaryExpr
case class Times(l: Expr, r: Expr) extends BinaryExpr
case class Div(l: Expr, r: Expr) extends BinaryExpr
case class Mod(l: Expr, r: Expr) extends BinaryExpr
// Monadic operation
case class Op(l: Expr, r: Expr) extends BinaryExpr
object Zero extends Expr
case class Reduce(range: Seq) extends Expr 

// Functions
sealed trait Funct extends Expr {
  // Create an application expression
  def apply(exprs: Expr*) = App(this, exprs.toList)
  // Replace operator by that
  def compose(that: Funct): Funct
  // Assume arguments are 0-arity; shift by expressions
  def >>(offset: Expr*) = {
    assert (arity > 0)
    assert (offset.size == arity)
    val args = (1 to arity).map(_ => Var.fresh()).toList
    OpVar(this, args, (args zip offset.toList).map {
        case (v, off) => v + off 
    })
  }
  // Create a translation expression
  def translate(args: List[Var], op: (Var, Expr)*) = {
    assert (arity > 0)
    val map = op.toMap
    val dargs = args.map(_.fresh)
    val exprs = (args zip dargs).map {
      case (arg, darg) => 
        if (map.contains(arg)) 
          map(arg).s(args zip dargs)
        else
          darg
    }
    OpVar(this, dargs, exprs)
  }
}

case class Var(name: String, override val arity: Int = 0) extends Funct {
  def fresh = Var.fresh(name, arity)

  def rename(s: String) = Var(s, arity)
  override def compose(that: Funct) = {
    assert (this.arity == that.arity, "composition disallowed")
    that
  }
}
object Var {
  private var counter = 0
  def fresh(prefix: String = "_v", arity: Int = 0) = {
    counter = counter + 1
    Var(prefix + counter, arity)
  }
}
case class OpVar(v: Funct, args: List[Var], exprs: List[Expr]) extends Funct {
  // it's important to keep args vars fresh to avoid naming collision
  assert(v.arity > 0, "must be a function")
  assert(v.arity == exprs.size, "wrong number of arguments in translation")
  override def arity = args.size
  override def compose(that: Funct) = OpVar(that, args, exprs)
  // Normalize to functor a pure Var
  def flatten: OpVar = App(this, args).flatten match {
    case App(w, wexprs) => OpVar(w, args, wexprs)
  }
}
case class App(v: Funct, args: List[Expr]) extends Expr {
  assert(v.arity == args.size, "wrong number of arguments in " + this)
  // Normalize to functor a pure Var
  def flatten: App = v match {
    case OpVar(v, vargs, vexprs) =>
      App(v, vexprs.map(_.s(vargs zip args))).flatten
    case _: Var => this
  }
}

// Sequence of (one-dimensional) values to be reduced
sealed trait Seq extends Term {
  def ++(that: Seq) = Join(this, that)
}
// Denotes empty seq if l >= h
case class Range(l: Expr, h: Expr) 
case class Compr(expr: Expr, v: Var, r: Range) extends Seq 
case class Join(l: Seq, r: Seq) extends Seq 
case class Singleton(e: Expr) extends Seq 

// Collect all variables
object Vars {
  def apply(t: Term): Set[Var] = t match {
    case True | False => Set() 
    case t: Comparison => apply(t.l) ++ apply(t.r)
    case t: BinaryPred => apply(t.l) ++ apply(t.r)
    case Not(p) => apply(p)
    case e: BinaryExpr => apply(e.l) ++ apply(e.r)
    case Zero | Havoc => Set()
    case _: Const => Set() 
    case Reduce(range) => apply(range)
    case v: Var => Set(v)
    case OpVar(v, args, exprs) => exprs.toSet[Expr].flatMap(apply(_)) ++ apply(v) -- args.toSet
    case App(v, args) => args.toSet[Expr].flatMap(apply(_)) ++ apply(v)
    case Compr(expr, v, Range(l, h)) => apply(expr) ++ Set(v) ++ apply(l) ++ apply(h)
    case Join(l, r) => apply(l) ++ apply(r)
    case Singleton(e) => apply(e)
    case Cond(cases, default) => 
      cases.flatMap { case (p, e) => apply(p) ++ apply(e) }.toSet ++
      apply(default)
  }
}
trait PythonPrinter {
  def prelude: String
  def print(s: Seq): String = s match {
    case Singleton(e) => "[" + print(e) + "]"
    case Join(l, r) => print(l) + " + " + print(r)
    case Compr(e, v, Range(l, h)) => "[" + print(e) + " for " + print(v) + 
      " in xrange(" + print(l) + ", " + print(h) + ")]"
  }
  def print(e: Expr): String = e match {
    case Var(n, _) => n
    case Const(i) => if (i >= 0) i.toString else "(- " + (-i).toString + ")"
    case Plus(l, r) => "(" + print(l) + " + " + print(r) + ")"
    case Minus(l, r) => "(" + print(l) + " - " + print(r) + ")"
    case Times(l, r) => print(l) + "*" + print(r)
    case Div(l, r) => print(l) + "/" + print(r)
    case Mod(l, r) => "(" + print(l) + " mod " + print(r) + ")"
    case App(v, args) => print(v) + "(" + args.map(print(_)).mkString(", ") + ")"
    case Op(l, r) => "plus(" + print(l) + ", " + print(r) + ")"
    case Reduce(r) => "reduce(plus, " + print(r) + ", zero)"
    case Zero => "zero"
    case Havoc => "None"
    case OpVar(v, args, exprs) => "(lambda " + args.map(print(_)).mkString(", ") + 
      ": " + print(v) + "(" + exprs.map(print(_)).mkString(", ") + "))"
    case Cond(cases, default) => cases match {
      case (pred, expr) :: rest => "(" + print(expr) + " if " + print(pred) + " else " + 
        print(Cond(rest, default)) + ")"
      case Nil => print(default)
    }  
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
  def print(c: Computation): String
  def print(p: List[Computation], out: java.io.PrintStream) {
    out.println(prelude)
    for (c <- p)
      out.println(print(c))
  }
}
// Functional style code output
object Python extends PythonPrinter {
  override val prelude = 
"""class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
    return self[args]
  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result
plus = min
zero = 10000000000000000000000000000
import random
import sys
sys.setrecursionlimit(2 ** 16)
"""
  def print(c: Computation): String = c match {
    case a: Algorithm =>
      "def " + print(a.v) +
      "(" + a.args.map(print(_)).mkString(", ") + "):\n" +     
      "  assert " + print(a.pre) + 
      "\n" + { a.expr match {
        case Cond(cases, default) => "  if " + cases.map { case (pred, expr) => 
          print(pred) + ":\n    return " + print(expr) }.mkString("\n  elif ") + 
          "\n  else:\n    return " + print(default)        
        case e => "  return " + print(e)
      }}
    case Input(v) => 
      if (v.arity == 0)
        print(v) + " = 16" 
      else 
        "@memoize\ndef " + print(v) + "(" + 
          (1 to v.arity).map("v"+_).mkString(", ") + "):\n" +
        "  return random.randint(0, 1000)" 
  }
}
object SMT {
  private var z3: Z3 = _

  import collection.mutable.ListBuffer
  def print(e: Expr)(implicit side: ListBuffer[String]): String = e match {
    case Var(n, k) if k == 0 => n
    // apply to variable witnesses
    case v: Funct  => print(App(v, (1 to v.arity).map(i => witness(i-1)).toList))
    case Const(i) => if (i >= 0) i.toString else "(- " + (-i).toString + ")"
    case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
    case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
    case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
    case Div(l, r) => 
      // TODO: can't easily express n is a power of two
      side += "(assert " + print((l mod r) === Const(0)) + ")"
      "(div " + print(l) + " " + print(r) + ")"
    case Mod(l, r) => "(mod " + print(l) + " " + print(r) + ")"
    case Zero => "zero"
    case Havoc =>
      val v = Var.fresh()
      side += "(declare-const " + v.name + " Int)"
      print(v)
    case Op(l, r) => "(plus " + print(l) + " " + print(r) + ")"
    case Reduce(r) => "(reduce " + print(r) + ")"
    case a: App => a.flatten match {
      case App(Var(n, k), args) => "(" + n + " " + args.map(print(_)).mkString(" ") + ")"
      case _ => ???
    }
    case Cond(cases, d) => cases match {
      case (p, e) :: rest=> "(ite " + print(p) + " " + print(e) + "\n " + print(Cond(rest, d)) + ")"
      case Nil => print(d)
    }
  }
  def print(s: Seq)(implicit side: ListBuffer[String]): String = s match {
    case Singleton(e) => "(singleton " + print(e) + ")"
    case Join(l, r) => "(join " + print(l) + " " + print(r) + ")"
    case Compr(e, v, Range(l, h)) => "(compr " + 
      print(e.s(List(v->(iterator+l)))) + " " + print(h-l) + ")"
  }
  def print(p: Pred)(implicit side: ListBuffer[String]): String = p match {
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

  // Special variables
  val iterator = Var("_i")
  val witness = (1 to 16).map(i => Var("_w" + i)).toList

  // Try to prove the negative
  def check(p: Pred) = ! prove(! p)

  // Prove the predicate by checking for counter example.
  // Returns true if the solver says "unsat" for !p, false if "sat" or "unknown"
  def prove(p: Pred) = {
    val side = new ListBuffer[String]
    for (v <- Vars(p)) {
      side += "(declare-fun " + v.name + 
        " (" + (1 to v.arity).map(_ => "Int").mkString(" ")+ ") Int)";
    }
    
    val formula = print(! p)(side)

    z3.push()
    for (s <- side)
      z3.command(s)
    z3.assert(formula)
    val out = z3.check()

    /*
    if (out) {
      println("cex: " + p)
      for (v <- Vars(p) if v.arity == 0)
        Console.out.print(eval(v.name))
      println()
    }
    */

    z3.pop()

    out == Unsat
  }

  def open() {
    z3 = new Z3
    z3.command("(declare-fun zero () Int)")
    z3.command("(declare-fun plus (Int Int) Int)")
    // substitute + for plus
    //z3.command("(define-fun plus ((a Int) (b Int)) Int (+ a b))")

    // zero for plus
    z3.command("(assert (forall ((x Int)) (= (plus x zero) x)))")
    z3.command("(assert (forall ((x Int)) (= (plus zero x) x)))")

    // plus is commutative
    z3.command("(assert (forall ((x Int) (y Int)) (= (plus x y) (plus y x))))")
    z3.command("(assert (forall ((x Int) (y Int) (z Int)) (= (plus x (plus y z)) (plus (plus x y) z))))") 

    // monoid
    z3.command("(declare-sort M)")
    z3.command("(declare-fun reduce (M) Int)")
    z3.command("(declare-fun join (M M) M)")
    z3.command("(declare-fun compr (Int Int) M)")

    // push reduce down
    z3.command("(assert (forall ((x M) (y M)) (= (reduce (join x y)) (plus (reduce x) (reduce y)))))")

    // eliminate singleton
    z3.command("(declare-fun singleton (Int) M)")
    z3.command("(assert (forall ((x Int)) (= (reduce (singleton x)) x)))")

    // eliminate empty comprehension
    z3.command("(assert (forall ((x Int)) (= (reduce (compr x 0)) zero)))")
 
    // iterator
    z3.command("(declare-fun " + iterator.name + " () Int)")
    
    // equality witnesses
    for (w <- witness) 
      z3.command("(declare-fun " + w.name + " () Int)")    
  }

  def close() {
    z3.close()
  }
}


object Transform {
  trait Transformer {
    def apply(path: Pred, p: Pred): Option[Pred] = None
    def apply(path: Pred, e: Expr): Option[Expr] = None
    def apply(path: Pred, s: Seq): Option[Seq] = None
  }
  def visit(p: Pred)(implicit path: Pred, f: Transformer): Pred = 
    f(path, p) match {
      case Some(out) => out
      case None => p match {
        case True => True
        case False => False
        case And(l, r) => And(visit(l), visit(r))
        case Or(l, r) => Or(visit(l), visit(r))
        case Not(l) => Not(visit(l))
        case Eq(l, r) => Eq(visit(l), visit(r))
        case LT(l, r) => LT(visit(l), visit(r))
        case GT(l, r) => GT(visit(l), visit(r))
        case LE(l, r) => LE(visit(l), visit(r))
        case GE(l, r) => GE(visit(l), visit(r))
      }
    }
  def visit(e: Expr)(implicit path: Pred, f: Transformer): Expr = { 
    f(path, e) match {
      case Some(out) => out
      case None => e match {
        case _: Var | _: Const | Zero | Havoc => e
        case Plus(l, r) => Plus(visit(l), visit(r))
        case Minus(l, r) => Minus(visit(l), visit(r))
        case Times(l, r) => Times(visit(l), visit(r))
        case Div(l, r) => Div(visit(l), visit(r))
        case Mod(l, r) => Mod(visit(l), visit(r))
        case App(v, args) => 
          App(visit(v).asInstanceOf[Funct], args.map(visit(_)))
        case Op(l, r) => Op(visit(l), visit(r))
        case Reduce(range) => Reduce(visit(range))
        case OpVar(v, args, exprs) => 
          OpVar(visit(v).asInstanceOf[Funct], 
            args.map(visit(_).asInstanceOf[Var]), 
            exprs.map(visit(_)))
        case Cond(cases, default) => 
          var els: Pred = path
          Cond(cases.map {
            case (p, e) => 
              val out = (visit(p)(els, f), visit(e)(els and p, f))
              els = els and !p
              out
          }, visit(default)(els, f))
      }
    }
  }
  def visit(s: Seq)(implicit path: Pred, f: Transformer): Seq = 
    f(path, s) match {
      case Some(out) => out
      case None => s match {
        case Compr(expr, v, Range(l, h)) => 
          Compr(visit(expr)(path and l <= v and v < h, f), 
            visit(v).asInstanceOf[Var], 
            Range(visit(l), visit(h)))
        case Join(l, r) => Join(visit(l), visit(r))
        case Singleton(e) => Singleton(visit(e))
      }
    }

  def transformer(f: PartialFunction[Term, Term]) = new Transformer {
    override def apply(path: Pred, p: Pred) = f.lift(p).asInstanceOf[Option[Pred]]
    override def apply(path: Pred, e: Expr) = f.lift(e).asInstanceOf[Option[Expr]]
    override def apply(path: Pred, s: Seq) = f.lift(s).asInstanceOf[Option[Seq]]
  }

  def exprTransformer(f: PartialFunction[(Pred, Expr), Expr]) = new Transformer {
    override def apply(path: Pred, e: Expr) =
      if (f.isDefinedAt((path, e)))
        Some(f((path, e)))
      else
        None
  }

  def seqTransformer(f: PartialFunction[(Pred, Seq), Seq]) = new Transformer {
    override def apply(path: Pred, e: Seq) =
      if (f.isDefinedAt((path, e)))
        Some(f((path, e)))
      else
        None
  }

  def transform(e: Expr)(f: PartialFunction[Term, Term]): Expr = 
    visit(e)(True, transformer(f))
  def transform(p: Pred)(f: PartialFunction[Term, Term]): Pred = 
    visit(p)(True, transformer(f))
  def substitute(e: Expr, f: Map[Var, Expr]): Expr = 
    transform(e) {
      case v: Var if f.contains(v) => f(v)
    }
  def substitute(p: Pred, f: Map[Var, Expr]): Pred =
    transform(p) {
      case v: Var if f.contains(v) => f(v)
    }    
  def flatten(e: Expr): Expr = transform(e) {
    case a: App => a.flatten match {
      case App(v, args) => App(v, args.map(flatten(_)))
    }
    case op: OpVar => op.flatten match {
      case OpVar(v, args, exprs) => OpVar(v, args, exprs.map(flatten(_)))
    }
  }
}

trait Environment extends Logger {
  // input tables
  var inputs: List[Input] = List()
  // algorithms
  var algorithms: List[Algorithm] = List()

  def input(v: Var) {
    inputs = Input(v) :: inputs
  }

  def add(alg: Algorithm) =
    algorithms.find(_.v == alg.v) match {
      case Some(old) if alg != old =>
        error("conflicting algorithms: " + alg + " and " + old)
      case None =>
        algorithms = alg :: algorithms
      case _ =>
    }

  def get(v: Var): Option[Computation] = 
    inputs.find(_.v == v) match {
      case Some(in) => Some(in)
      case None => algorithms.find(_.v == v) match {
        case Some(alg) => Some(alg)
        case None => None
      }
    }
    
  // Refinement chains (v, op, w) where v is refined by w
  // and op.v = w so that v(args) = op(args)
  var refines: List[(Algorithm, Funct, Algorithm)] = Nil

  // Restrictions
  // (v, w) where w has stronger pre-condition but computes same thing
  var restricts: List[(Algorithm, Algorithm)] = Nil

  type Refinement = Algorithm => Algorithm

  // Add a refinement step
  def step0(f: Algorithm => (Algorithm, Funct)): Refinement = { 
    (in: Algorithm) => {    
      val (out, stp) = f(in)
      message(in.v + " refined to " + out.v)
      
      add(in)
      refines = (in, stp, out) :: refines
      add(out)

      out
    }
  }

  def step(f: Refinement): Refinement = step0 { 
    (in: Algorithm) => val out = f(in); (out, out.v) 
  }

  // attempt to follow down refinement chain
  def lift(from: Var, to: Var): Option[Funct] = {
    for ((k, op, l) <- refines
        if k.v == from) 
      if (l.v == to)
        return Some(op)
      else lift(l.v, to) match {
        case Some(op2) => 
        return Some(op compose op2)
        case _ =>
      }
            
    None
  }

  // Compilation
  import java.io.PrintStream
  import Transform._

  def showGraph() {
    GraphViz.display { 
      refines.map(s => (s._1, s._2.toString, s._3)) ::: 
      restricts.map(s => (s._1, "?split", s._2))
    }
  }

  def leaves: List[Algorithm] = 
    algorithms.filter { a => ! refines.exists(_._1 == a) }

  // Push down algorithms down the refinement chain to the leafs
  // TODO: global termination checks (especially in splits)
  def refineAll: List[Algorithm] = {
    // TODO: hack to avoid obvious self-loops
    var keep: List[Algorithm] = Nil

    // stack awareness
    def lower(s: List[Var], e: Expr)(implicit ctx: Algorithm): Expr = transform(e) {
      case v: Var if ! s.contains(v) => 
        if (inputs.exists(_.v == v) || leaves.exists(_.v == v)) 
          v
        else leaves.find { a => lift(v, a.v).isDefined } match {
          case Some(a) => 
            if (a == ctx) {
              message("WARNING: keeping " + v + " in " + ctx.v)
              keep = algorithms.find(_.v == v).get :: keep
              v
            } else
              lower(s, lift(v, a.v).get)
          case None => 
            error("can't locate leaf for " + v)
            v
        }
      case OpVar(v, vargs, exprs) => 
        OpVar(lower(s, v).asInstanceOf[Funct], vargs, exprs.map(lower(vargs ::: s, _)))
      case Compr(expr, v, Range(l, h)) => 
        Compr(lower(v :: s, expr), v, Range(lower(s, l), lower(s, h)))
    }
  
    // modify bodies to refer only to leaves
    val out = for (leaf @ Algorithm(v, args, pre, e) <- leaves)  
      yield Algorithm(v, args, pre, flatten(lower(args, e)(leaf)))
      
    out ::: keep
  }

  // Generalize arguments by adding offsets to every argument function
  // Assumes argument functions do not take functions as parameters
  def offsettify(p: List[Algorithm]) = {    
    // STAGE ONE

    def offsets(v: Var) = {
      assert (v.arity > 0)
      for (i <- 0 to v.arity - 1) 
        yield Var(v.name + "_" + i)
    }

    // extended argument list
    def extended(args: List[Var]) = args ::: {
      for (v <- args if v.arity > 0;
           arg <- offsets(v))
        yield arg
    }

    def extend(e: Expr)(implicit args: List[Var]): Expr = transform(e) {
      case v: Var if v.arity > 0 =>
        if (args.contains(v)) 
          v >> (offsets(v):_*)
        else if (inputs.exists(_.v == v))
          v
        else p.find(_.v == v) match {
          case Some(a) =>
            val args1 = extended(a.args)            
            a.lift(Var(a.v.name, args1.size))(1 to (args1.size - a.args.size) map (_ => Const(0)) :_*)
          case None => 
            error("unknown variable: " + v)
            ???
        }
    }    

    // add offset arguments to inputs and all applications
    val p1 = 
      for (Algorithm(v, args, pre, e) <- p;
           args1 = extended(args))                  
        yield Algorithm(Var(v.name, args1.size), args1, pre, extend(e)(args))
  
    // STAGE TWO

    // Make use of offsets to eliminate OpVars
    def linearize(e: Expr): Expr = transform(flatten(e)) {
      case App(v, vargs) if p1.exists(_.v == v) =>
        val a = p1.find(_.v == v).get
        val args = vargs.map(linearize)

        var offsets: List[(Var, Expr)] = Nil
        val linearized = (a.args zip args) map {
          case (formal, actual: OpVar) => Linear.offsets(actual) match {
            case Some((w, offs)) => 
              offsets :::= offs.zipWithIndex.map { 
                case (o, i) => (Var(formal.name + "_" + i), o) 
              }
              w              
            case None => 
              println("can't linearize " + actual)
              actual            
          }
          case (_, actual) => actual
        }
        val combined = (a.args zip linearized) map {
          case (formal, actual) => actual + offsets.toMap.getOrElse(formal, Const(0))
        }
        App(v, combined)
      case op @ OpVar(v, args, exprs) if p1.exists(_.v == v) => 
        linearize(App(op, args)) match {
          case App(w, wargs) => 
            assert(w == v)
            OpVar(v, args, wargs)
          case _ => ???
        }
    }

    val p2 = for (Algorithm(v, args, pre, e) <- p1)
      yield Algorithm(v, args, pre, linearize(e))

    p2
  }

  // hack to avoid non-termination for now
  def compile(main: Algorithm, out: PrintStream = Console.out, 
      printer: PythonPrinter = Python) {
    //showGraph()     
    val all = main :: inputs ::: offsettify(refineAll)
    printer.print(all, out)
  }
}

/**
 * Refinement steps
 */
class Proof extends Environment {
  import Transform._

  def $ = Var.fresh().name
  def $$ = new Proof

  // Check induction
  // todo: global induction
  def induction(a: Algorithm, metric: Expr, base: Expr) {
    visit(a.expr)(a.pre, exprTransformer {
      case (path, app @ App(v, args)) if v == a.v =>
        if (! SMT.prove(path implies (metric.s(a.args zip args) < metric))) 
          error("failed induction check on " + a.v + " at " + app)         
        app
    })
    
    if (! SMT.prove(a.pre implies (base <= metric)))
      error("failed base case check")
  }

  // check for pre-conditions
  def welldefined(pre: Pred, e: Expr) = {
    ???
  }
  
  // Identity
  def id: Refinement = identity[Algorithm]

  // Substitute the body of an algorithm
  def manual(name: String, body: Expr, hint: Refinement = id) = step {
    case in @ Algorithm(v, args, pre, e) =>
      val out = Algorithm(v.rename(name), args, pre, body)
      val out1 = hint(out)
      if (! SMT.prove(pre implies (e === out1.expr))) {        
        error("failed to prove equivalence of body expressions")
        in
      } else
        out
  }

  // Add parameters to a function 
  def introduce(name: String, vs: Var*) = step0 {
    case a @ Algorithm(v, args, pre, e) => 
      val w = Var(name, v.arity + vs.size)
      (Algorithm(w, args ++ vs.toList, pre, e), a.lift(w)(vs.toList:_*))
  }

  // Push self-application down the refinement chain
  // todo check termination
  def selfRefine(name: String) = step {
    case Algorithm(v, args, pre, e) =>
      val w = v.rename(name)        
      def push(e: Expr): Expr = transform(e) {
        case App(u: Var, uargs) if lift(u, v).isDefined =>
          //  App(lift(u, v).get compose w, uargs.map(push(_))).flatten
          App(w, uargs.map(push(_)) ++ args.drop(uargs.size))
      }
      Algorithm(w, args, pre, push(e))
  }

  // Push functions down refinement chain
  // todo: check termination
  def refine(name: String, from: Var, to: Var) = step {
    case Algorithm(v, args, pre, e) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, transform(e) {
        case App(u: Var, uargs) if u == from && lift(from, to).isDefined =>
          App(lift(from, to).get, uargs).flatten
      })
  }

  // Specialize application of c0 to its immediate version
  def specialize(name: String, c0: Algorithm) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      def push(path: Pred, e: Expr): Expr = 
        visit(e)(path, exprTransformer {
          case (path, App(u, uargs)) if u == c0.v =>      
            restricts.find {
              case (a, c1) => 
                a == c0 && SMT.prove(path implies c1.pre.s(c1.args zip uargs)) 
            } headOption match {
              case Some((_, c1)) => App(c1.v, uargs)
              case None => App(c0.v, uargs)
            }
        }) 
      Algorithm(w, args, pre, push(pre, expr))
  }

  // Create specialized versions of alg by splitting the domain
  def split(name: String, base: Pred, splits: Pred*): Algorithm => List[Algorithm] = {
    case a @ Algorithm(v, args, pre, e) =>
      var cases: List[(Pred, Expr)] = Nil;
      var algs: List[Algorithm] = Nil;

      var out = IF (base -> App(v, args))

      def explore(mask: List[Boolean] = Nil) {
        if (mask.size == splits.size) {
          val p = (mask.reverse zip splits.toList) map {
            case (b, split) => if (b) split else !split
          } reduce (_ and _)

          if (SMT.check(p and pre)) {
            val n = v.name + mask.reverse.map(if (_) "0" else "1").mkString
            val cs = Algorithm(Var(n, v.arity), args, pre and p, App(v, args))
            out = out ELIF (p -> App(cs.v, args))
            algs = cs :: algs        
          }
        } else {
          explore(true :: mask)
          explore(false :: mask)
        }
      }
      explore()
      algs = algs.reverse

      val alg = Algorithm(Var(name, v.arity), args, pre, out) 
     
      // update environment

      add(alg)
      refines = (a, alg.v, alg) :: refines

      for (a0 <- algs) {
        add(a0)
        restricts = (a, a0) :: restricts
      }

      alg :: algs
  }

  // Rewrite calls to c as d = OpVar(c,...) provided substitution
  // is correct under path condition
  def rewrite(name: String, ov: Algorithm, 
    hint1: Refinement = id, hint2: Refinement = id)(ve: (Var, Expr)*) =
    rewrite0(name, ov, ov, ov.v, hint1, hint2)(ve: _*)

  def rewrite0(name: String, ov: Algorithm, nv: Algorithm, lift: Funct, 
    hint1: Refinement = id, hint2: Refinement = id)(ve: (Var, Expr)*) = {
    val op = lift compose nv.v.translate(nv.args, ve: _*)
    step {
      case Algorithm(v, args, pre, e) =>
        val w = v.rename(name)
        Algorithm(w, args, pre, 
          visit(e)(pre, exprTransformer {
            case (path, App(w, args)) if w == ov.v && 
              inductiveProof(path, ov, nv, op, hint1, hint2) =>
              (App(op, args).flatten)
          }))
    }
  }


  var SKIP_FIRST = false
    
  // Prove by induction that pred(v) => c(v) = c(f(v)) where d = OpVar(c, f)
  def inductiveProof(pred: Pred, ov: Algorithm, nv: Algorithm, op: Funct, 
    hint1: Refinement, hint2: Refinement): Boolean = {
    // check domains: d is well defined for substitution
    val domain = (pred and ov.pre) implies nv.pre.s(nv.args zip App(op, ov.args).flatten.args)
    if (! SMT.prove(domain)) {
      error("failed domain check")
      return false
    }

    // apply proof hint and get expression
    val oexpr = flatten(hint1(Algorithm(ov.v, ov.args, pred and ov.pre, ov.expr)).expr)

    // prove by induction on v (c's metric)
    // inductive step
    var skip = SKIP_FIRST
    val oind = flatten(visit(oexpr)(pred and ov.pre, exprTransformer {
      case (path, app @ App(v, args)) if v == ov.v => 
        if (SMT.check(path and ! pred.s(ov.args zip args))) {
          // violation of the inductive step predicate
          app
        } else {          
          if (skip) {
            // force skip for base case
            skip = false
            app
          } else {
            // by induction hypothesis
            App(op, args)
          }
        }
    }))
    val nind = flatten(hint2(Algorithm(nv.v, nv.args, pred and nv.pre, 
      nv.expr.s(nv.args zip App(op, ov.args).flatten.args))).expr)
  
    if (! SMT.prove((pred and ov.pre) implies (oind === nind))) {
      message("pred")
      println(pred)
      message("oind")
      println(oind)
      message("nind")
      println(nind)
      error("failed to prove equation equality")
      return false
    }
   
    return true
  }

  // Unroll application to c
  def unfold(name: String, c: Algorithm) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, visit(flatten(expr))(pre, exprTransformer {
        case (path, App(w, wargs)) if w == c.v =>
          if (! SMT.prove(path implies c.pre.s(c.args zip wargs))) {
            println("path: " + path)
            println("pre: " + c.pre.s(c.args zip wargs))
            error("violation of pre-condition in unfolding of " + c.v)          
          }
          c.expr.s(c.args zip wargs)
      }))
  }
        
  // Split "k in range(a,b)" into "k1 in range(a,e) and k2 in range(e,b)"
  def splitRange(name: String, k: Var, mid: Expr) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, visit(expr)(pre, seqTransformer {
        case (path, compr @ Compr(e, v, Range(l, h))) if v == k => 
          if (! SMT.prove(path implies (l <= mid and mid <= h))) {
            error("can't split range since value may lay outside of range")
            compr
          } else {
            val v1 = Var(v.name + "1")
            val v2 = Var(v.name + "2")
            Join(Compr(substitute(e, Map(v->v1)), v1, Range(l, mid)), 
                Compr(substitute(e, Map(v->v2)), v2, Range(mid, h)))
          }
      }))
  }

  // Fix a value for which old function symbol is used
  def guard(name: String, pred: Pred) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, IF (pred -> v(args:_*)) ELSE expr)
  }

  // Generalize pre-condition
  // TODO: welldefinedness check
  def relax(name: String, pred: Pred) = step {
    case a @ Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      val pre1 = 
        if (! SMT.prove(pre implies pred)) {
          error("cannot relax precondition " + pre + " to " + pred)
          pre
        } else {
          pred
        }
      Algorithm(w, args, pre1, expr)
  }

  // Generalize variable application 
  // Find "which" application of "ov" and replace by "nv" with lower arity
  def genApp(name: String, ov: Var, nv: Var, which: Int = 0) = step0 {
    case a @ Algorithm(v, args, pre, e) =>
      assert (nv.arity <= ov.arity)
      val w = Var(name, v.arity + 1)
      var op: Option[OpVar] = None
      var i = -1
      (Algorithm(w, args :+ nv, pre, transform(e) {
        case app @ App(u: Var, uargs) if u == ov =>
          i = i + 1
          if (i == which) {
            val nvargs = uargs.take(nv.arity)
            val nvargs1 = nvargs.map(v => Var.fresh(arity = v.arity))
            op = Some(OpVar(ov, nvargs1, nvargs1 ++ uargs.drop(nv.arity)))
            App(nv, nvargs)
          } else {
            app
          }          
      }), a.lift(w)(op match {
          case Some(op) => op           
          case None => nv
        }))
    }
}

trait Unification {
  // Complete OpVar of c based on op
  import collection.mutable.ListBuffer

  // Relaxed unification
  def unify(c: Term, d: Term)(implicit eqs: ListBuffer[Pred]) {
    (c, d) match {
      case (c: BinaryPred, d: BinaryPred) if c.getClass == d.getClass =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case (Not(c), Not(d)) => unify(c, d)
      case (c: Comparison, d: Comparison) if c.getClass == d.getClass =>
        unify(c.l - c.r, d.l - d.r)       
      case (c: Cond, d: Cond) if c.cases.size == d.cases.size =>
        for (((cp, ce), (dp, de)) <- c.cases zip d.cases) {
          unify(cp, dp)
          unify(ce, de)
        }
        unify(c.default, d.default)
      case (c: Reduce, d: Reduce) =>
        unify(c.range, d.range)
      case (c: Join, d: Join) =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case (Singleton(c), Singleton(d)) => unify(c, d)
      case (c: Compr, d: Compr) =>
        unify(c.r.h - c.r.l, d.r.h - d.r.l)
        unify(c.expr.s((c.v, c.r.l)::Nil), d.expr.s((d.v, d.r.l)::Nil))
      case (c: App, d: App) =>
        eqs += (c.flatten === d.flatten)
      case (c: Expr, d: Expr) if Linear(c).isDefined && Linear(d).isDefined =>
        eqs += (c === d)
      case (c: BinaryExpr, d: BinaryExpr) if c.getClass == d.getClass =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case _ =>
    }
  }

}

object Parenthesis {
  import Prelude._
  import java.io.{PrintStream, File}
  implicit def int2expr(i: Int) = Const(i)

  val w = Var("w", 3)
  val x = Var("x", 1)
  
  val c = Var("c", 2)
  val par = Algorithm(c, i :: j :: Nil,
    0 <= i and i < n and i < j and j < n,
    IF ((i === j-1) -> x(i)) 
    ELSE
      Reduce(c(i, k) + c(k, j) + w(i, k, j) 
      where k in Range(i+1, j)))

   
  def main(args: Array[String]) {
    SMT.open()
    val proof = new Proof()
    import proof._

    val loops = new LoopConstruct(par, 2)
    loops.generate
    
    input(w)
    input(x)
    input(n)
    add(par)
    induction(par, j-i, 1)

    val r = Var("r", 2)
    val R = Algorithm(r, List(i, j), True, IF ((i === j-1) -> x(i)) ELSE Zero)
    add(R)

    val par0 = manual($, 
      Op(Reduce(c(i, k) + c(k, j) + w(i, k, j) where k in Range(i+1, j)), r(i, j)),
      $$.unfold($, R))(par)

    val c0 = (introduce($, n, w, r) andThen 
      selfRefine("c0"))(par0)    
    val List(c1, c000, c001, c011) = split("c1", n < 4, i < n/2, j < n/2)(c0) 
  
    val c100 = rewrite("c100", c0)(n -> n/2)(c000) 
    // use free assumption n mod 2 = 0    
    val c111 = rewrite("c111", c0)(
        i->(i-n/2), 
        j->(j-n/2), 
        n->n/2, 
        w->(w>>(n/2,n/2,n/2)), 
        r->(r>>(n/2,n/2))
      )(c011)

    // We have to make a very general version of b0 to make proofs work
    val s = Var("s", 2)
    val t = Var("t", 2)
    val w1 = Var("w1", 3)
    val b0 = (unfold($, c0) andThen
      splitRange($, k, n/2) andThen
      specialize($, c0) andThen
      genApp($, c000.v, s) andThen 
      genApp($, c011.v, t) andThen
      genApp($, w, w1) andThen
      selfRefine("b0"))(c001)
   
    val List(b1, b000, b001, b010, b011) = split("b1", n < 4, i < n/4, j < n/2+n/4)(b0)
       
    val b110 = rewrite("b110", b0)(
        i->(i-n/4),
        j->(j-n/4),
        n->n/2,
        w->(w>>(n/4,n/4,n/4)),
        w1->(w1>>(n/4,n/4,n/4)),
        s->(s>>(n/4,n/4)),       
        t->(t>>(n/4,n/4)),
        r->(r>>(n/4,n/4))
      )(b010)

    // define d
    val d = Var("d", 7)
    val D = Algorithm(d, List(i, j, n, w, r, s, t), 0 < n,
      Op(Reduce(s(i, k) + t(k, j) + w(i, k, j) where k in Range(0, n/2)), r(i, j)))
    add(D)
     
    val bij = b0.capture(2) 
   
    // TODO: violation of D precondition on Op

    // we can infer i and j displacements by looking at pre-condition of b0 and case of b000   
    val b100 = rewrite("b100", b0, $$.splitRange($, Var("k1"), n/4), $$.unfold($, D))(
        i->i,
        j->(j-n/4),
        n->n/2,        
        w->(w>>(0,n/4,n/4)),
        w1->(w1>>(0,0,n/4)),        
        t->(t>>(n/4,n/4)),
        r->D.gen(2)(i, j-n/4, n/2, w1>>(0,n/4,n/2), 
          r>>(0,n/2),s>>(0,n/4),bij>>(n/4,n/2))          
      )(b000)
    val b111 = rewrite("b111", b0, $$.splitRange($, Var("k2"), n/4+n/2), $$.unfold($, D))(
        i->(i-n/4),
        j->(j-n/2),
        s->(s>>(n/4,n/4)),
        t->(t>>(n/2,n/2)),
        w->(w>>(n/4,n/2,n/2)),
        w1->(w1>>(n/4,n/4,n/2)),
        n->n/2,
        r->D.gen(2)(i+n/4, j+n/2, n/2, w>>(0,n/2,0),
          r, bij>>(0,n/2), t>>(n/2,0))
      )(b011)
    val b101 = rewrite("b101", b0, 
        $$.splitRange($, Var("k1"), n/4) andThen $$.splitRange($, Var("k2"), n/4+n/2),
        $$.unfold($, D) andThen $$.unfold($, D))(
        j->(j-n/2),
        n->n/2,
        s->s,
        w1->(w1>>(0,0,n/2)),
        t->(t>>(n/2,n/2)),
        w->(w>>(0,n/2,n/2)),
        r->D.gen(2)(i, j+n/2, n/2, w1>>(0,n/4,0),
          D.gen(2)(i, j, n/2, w>>(0,n/2,0), r, bij>>(0,n/2), t>>(n/2,0)), 
          s>>(0,n/4), bij>>(n/4,0))        
      )(b001)

    val List(d1, d00, d01, d10, d11) = split("d1", n < 4, i < n/4, j < n/4)(D)
    val d100 = rewrite("d100", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      n->n/2, 
      r->D.gen(2)(i,j,n/2,w>>(0,n/4,0),r,s>>(0,n/4),t>>(n/4,0))
    )(d00)
    val d110 = rewrite("d110", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      i->(i-n/4), n->n/2, 
      r->D.gen(2)(i, j, n/2, w>>(n/4,0,0), r>>(n/4,0), s>>(n/4,0), t),
      w->(w>>(n/4,n/4,0)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,0))
    )(d10)
    val d101 = rewrite("d101", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      j->(j-n/4), n->n/2,
      r->D.gen(2)(i, j, n/2, w>>(0,0,n/4), r>>(0,n/4), s, t>>(0, n/4)),
      w->(w>>(0,n/4,n/4)),
      s->(s>>(0,n/4)),
      t->(t>>(n/4,n/4))
    )(d01)
    val d111 = rewrite("d111", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      i->(i-n/4), j->(j-n/4), n->n/2,
      r->D.gen(2)(i, j, n/2, w>>(n/4,0,n/4), r>>(n/4,n/4), s>>(n/4,0), t>>(0,n/4)),
      w->(w>>(n/4,n/4,n/4)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,n/4))
    )(d11)


    val py = new NumPython(2, """|  for df in xrange(1, n): 
                                 |    for i in xrange(0, n-df):
                                 |      j = i + df""".stripMargin)
    
    compile(par, new PrintStream(new File("paren.py")), py)
    SMT.close()
  }
}

object Gap {
  import Prelude._
  implicit def int2expr(i: Int) = Const(i)
  implicit def expr2singleton(e: Expr) = Singleton(e)

  val w = Var("w", 2)
  val w1 = Var("w1", 2)
  val S = Var("S", 2)
  val g = Var("g", 2)

  val G = Algorithm(g, i :: j :: Nil,
    0 <= i and i <= n and 0 <= j and j <= n,
    IF  
      ((i === 0 and j === 0) -> 0)
    ELIF 
      ((i === 0 and j > 0) -> w(0, j))
    ELIF 
      (((i > 0 and j === 0) -> w1(0, i)))
    ELSE 
      Reduce(
        (g(i, q) + w(q, j) where q in Range(0, j)) ++
        (g(p, j) + w1(p, i) where p in Range(0, i)) ++
        (g(i-1, j-1) + S(i, j))))
}

object Floyd {
  import Prelude._
  import java.io.{File, PrintStream}
  implicit def int2expr(i: Int) = Const(i)

  val r = Var("r", 2)
  val f = Var("f", 3)

  val F = Algorithm(f, i :: j :: k :: Nil,
    0 <= i and i < n and
    0 <= j and j < n and
    0 <= k and k <= n,
    IF 
      ((k === 0) -> r(i, j))
    ELSE 
      (f(i, j, k-1) + f(i, k-1, k-1) * f(k-1, j, k-1)))

  def main(args: Array[String]) {
    SMT.open()
    val proof = new Proof()    
    import proof._

    input(r)
    input(n)
    add(F)
    induction(F, k, 0)

    val a = (introduce($, n, r) andThen selfRefine("a"))(F)
    val List(a1, a000, a001, a010, a011, a100, a101, a110, a111) = split("a1", n < 2,
        i < n/2, j < n/2, k <= n/2)(a)

    val x = (unfold($, a) andThen specialize($, a) andThen selfRefine("x"))(a000)
   
    // generalize x
    val s = Var("s", 3)
    val t = Var("t", 3)
    val b = (genApp($, x.v, s, 1) andThen selfRefine("b"))(x)
    val c = (genApp($, x.v, s, 2) andThen selfRefine("c"))(x)
    val d = (genApp($, b.v, t, 1) andThen selfRefine("d"))(b)

    // cases for b
    val List(b1, b000, b001, b010, b011, b100, b101, b110, b111) = split("b1", n < 4, 
        i < n/4, j < n/4, k < n/4)(b)
    
    val b000x = rewrite("b000x", b)(n -> n/2)(b000)
    val b010x = rewrite("b010x", b)(
      j->(j-n/4), n->n/2, r->(r>>(0, n/4)))(b010)
    val b100x = (refine($, b.v, d.v) andThen rewrite("b100x", d)(
      i->(i-n/4), n->n/2, r->(r>>(n/4, 0)), s->(s>>(n/4,0,0))))(b100)
    val b110x = (refine($, b.v, d.v) andThen rewrite("b110x", d)(
      i->(i-n/4), j->(j-n/4), n->n/2, r->(r>>(n/4,n/4)), 
      s->(s>>(n/4,0,0)), t->(t>>(0,n/4,0))))(b110)
    
    SKIP_FIRST = true
    // k = n/4 should be in the first case
    val b101x = rewrite("b101x", b, $$.guard($, k === n/4))(
      i->(i-n/4), k->(k-n/4), n->n/2, 
      s->(s>>(n/4,n/4,n/4)), 
      r->b.gen(2)(i+n/4, j, n/4, n, r, s))(b101)
    val b111x = rewrite("b111x", b, $$.guard($, k === n/4))(
      i->(i-n/4), j->(j-n/4), k->(k-n/4), n->n/2,
      s->(s>>(n/4,n/4,n/4)),
      r->b.gen(2)(i+n/4, j+n/4, n/4, n, r, s))(b111)
    val b001x = (refine($, b.v, d.v) andThen 
      rewrite("b001x", d, $$.guard($, k === n/4))(
      k->(k-n/4), n->n/2,
      s->(s>>(0,n/4,n/4)),
      t->(t>>(n/4,0,n/4)),
      r->d.gen(2)(i, j, n/4, n, r, s, t)
      ))(b001)
    val b011x = (refine($, b.v, d.v) andThen
      rewrite("b011x", d, $$.guard($, k === n/4))(
      j->(j-n/4), k->(k-n/4), n->n/2,
      s->(s>>(0,n/4,n/4)),
      t->(t>>(n/4,n/4,n/4)),
      r->d.gen(2)(i, j+n/4, n/4, n, r, s, t)
      ))(b011)
    SKIP_FIRST = false
 
    // lift version of a
    val k0 = k.fresh
    val ax = a.capture(3)
    val amid = a.gen(2)(i, j, n/2, n, r)

    // cases for a
    
    val a000x = rewrite("a000x", a)(n -> n/2)(a000)
    val a010x = rewrite0("a010x", a, b, a.lift(b.v)(ax))(
      j->(j-n/2), r->(r>>(0,n/2))
    )(a010)
    val a100x = rewrite0("a100x", a, c, a.lift(c.v)(ax))(
      i->(i-n/2), r->(r>>(n/2,0))
    )(a100)
    val a110x = rewrite0("a110x", a, d, a.lift(d.v)(ax>>(n/2,0,0), ax>>(0,n/2,0)))(
      i->(i-n/2), j->(j-n/2), r->(r>>(n/2,n/2))
    )(a110)
    SKIP_FIRST = true
    val a111x = (relax($, a.pre and i >= n/2 and j >= n/2 and k >= n/2) andThen 
      rewrite("a111x", a, $$.guard($, k === n/2))(
        i->(i-n/2), j->(j-n/2), k->(k-n/2), n->n/2, r->(amid>>(n/2, n/2))
      ))(a111)
    val a011x = (relax($, a.pre and i < n/2 and j >= n/2 and k >= n/2) andThen
      rewrite0("a011x", a, c, a.lift(c.v)(ax>>(n/2,n/2,n/2)), $$.guard($, k === n/2))(
        j->(j-n/2), k->(k-n/2), r->(amid>>(0,n/2))
      ))(a011)
    val a101x = (relax($, a.pre and i >= n/2 and j < n/2 and k >= n/2) andThen
      rewrite0("a101x", a, b, a.lift(b.v)(ax>>(n/2,n/2,n/2)), $$.guard($, k === n/2))(
        i->(i-n/2), k->(k-n/2), r->(amid>>(n/2,0))
      ))(a101)
    val a001x = (relax($, a.pre and i < n/2 and j < n/2 and k >= n/2) andThen
      rewrite0("a001x", a, d, a.lift(d.v)(ax>>(0,n/2,n/2), ax>>(n/2,0,n/2)), $$.guard($, k === n/2))(
        k->(k-n/2), r->amid
      ))(a001) 

    SKIP_FIRST = false

    compile(F, new PrintStream(new File("floyd.py")))
    SMT.close()
  }
}


object Prelude {
  val i = Var("i")
  val j = Var("j") 
  val k = Var("k")
  val l = Var("l")
  val m = Var("m")
  val n = Var("n")
  val o = Var("o")
  val p = Var("p")
  val q = Var("q")
}
