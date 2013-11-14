sealed trait Term 

// Recursive algorithm definition
case class Algorithm(v: Var, args: List[Var], pre: Pred, expr: Expr) {
  assert (v.arity == args.size)
  override def toString = Python.print(this)
  def lift(that: Algorithm)(rest: Expr*) =
    OpVar(that.v, args, args ++ rest.toList)
  def translate(op: (Var, Expr)*) = 
    v.translate(args, op: _*)
}


// Boolean predicate
sealed trait Pred extends Term {
  def and(that: Pred): Pred = that match {
    case True => this
    case _ => And(this, that)
  }
  def or(that: Pred): Pred = that match {
    case False => this
    case _ => Or(this, that)
  }
  def implies(that: Pred): Pred = (! this) or that
  def unary_! = Not(this)  
  override def toString = Python.print(this)
  def s(subs: List[(Var, Expr)]) = 
    Transform.substitute(this, subs.toMap)
}
object True extends Pred {
  override def and(that: Pred) = that
}
object False extends Pred {
  override def or(that: Pred) = that
}
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
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)
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
  def apply(exprs: Expr*) = App(this, exprs.toList)
  // subsequent compositions rewrite "v" in the operator
  def compose(that: Funct): Funct
  def v: Var
  // assume arguments are 0-arity
  def >>(offset: Expr*) = {
    assert (offset.size == arity)
    val args = (1 to arity).map(_ => Var.fresh()).toList
    OpVar(Var.fresh(">>", arity), args, (args zip offset.toList).map {
        case (v, off) if off == Const(0) => v
        case (v, off) => v + off 
    }) compose this
  }
}
case class Var(name: String, override val arity: Int = 0) extends Funct {
  def fresh = Var.fresh(name, arity)
  // Translate argument list
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
  def rename(s: String) = Var(s, arity)
  override def compose(that: Funct) = {
    assert (this.arity == that.arity, "composition disallowed")
    that
  }
  override def v = this
}
object Var {
  private var counter = 0
  def fresh(prefix: String = "_v", arity: Int = 0) = {
    counter = counter + 1
    Var(prefix + counter, arity)
  }
}
case class OpVar(v: Var, args: List[Var], exprs: List[Expr]) extends Funct {
  assert(v.arity > 0, "must be a function")
  assert(v.arity == exprs.size, "wrong number of arguments in translation")
  override def arity = args.size
  override def compose(that: Funct) = that match {
    case w: Var => OpVar(w, args, exprs)
    case OpVar(w, wargs, wexprs) => OpVar(w, args, wexprs.map(_.s(wargs zip exprs)))
  }
}
case class App(v: Funct, args: List[Expr]) extends Expr {
  assert(v.arity == args.size, "wrong number of arguments in " + this)
  def flatten = v match {
    case OpVar(v, vargs, vexprs) =>
      App(v, vexprs.map(_.s(vargs zip args)))
    case _ => this
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
    case OpVar(v, args, exprs) => exprs.toSet[Expr].flatMap(apply(_)) ++ Set(v) -- args.toSet
    case App(v, args) => args.toSet[Expr].flatMap(apply(_)) ++ apply(v)
    case Compr(expr, v, Range(l, h)) => apply(expr) ++ Set(v) ++ apply(l) ++ apply(h)
    case Join(l, r) => apply(l) ++ apply(r)
    case Singleton(e) => apply(e)
    case Cond(cases, default) => 
      cases.flatMap { case (p, e) => apply(p) ++ apply(e) }.toSet ++
      apply(default)
  }
}

object Python {
  val prelude = 
"""
#!/usr/bin/python
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

import random
import sys
sys.setrecursionlimit(2 ** 16)
"""
  // translate into python list/generator
  def print(s: Seq): String = s match {
    case Singleton(e) => "[" + print(e) + "]"
    case Join(l, r) => print(l) + " + " + print(r)
    case Compr(e, v, Range(l, h)) => "[" + print(e) + " for " + print(v) + 
      " in range(" + print(l) + ", " + print(h) + ")]"
  }
  def print(e: Expr): String = e match {
    case Var(n, _) => n
    case Const(i) => i.toString
    case Plus(l, r) => "(" + print(l) + " + " + print(r) + ")"
    case Minus(l, r) => "(" + print(l) + " - " + print(r) + ")"
    case Times(l, r) => print(l) + "*" + print(r)
    case Div(l, r) => print(l) + "/" + print(r)
    case Mod(l, r) => "(" + print(l) + " mod " + print(r) + ")"
    case App(v, args) => print(v) + "(" + args.map(print(_)).mkString(", ") + ")"
    case Op(l, r) => "plus(" + print(l) + ", " + print(r) + ")"
    case Reduce(r) => "reduce(plus, " + print(r) + ")"
    case Zero => "zero"
    case Havoc => "None"
    case OpVar(v, args, exprs) => "(lambda " + args.map(print(_)).mkString(", ") + 
      ": " + print(v) + "(" + exprs.map(print(_)).mkString(", ") + ")"

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
  def print(a: Algorithm): String = {
    "@memoize\ndef " + print(a.v) +
    "(" + a.args.map(print(_)).mkString(", ") + "):\n" +     
    "  assert " + print(a.pre) + 
    "\n" + { a.expr match {
      case Cond(cases, default) => "  if " + cases.map { case (pred, expr) => 
        print(pred) + ":\n    " + print(expr) }.mkString("\n  elif ") + 
        "\n  else:\n    " + print(default)        
      case e => "  return " + print(e)
    }}
  }
}

object SMT {
  private var z3: Z3 = _

  import collection.mutable.ListBuffer
  def print(e: Expr)(implicit side: ListBuffer[String]): String = e match {
    case Var(n, k) if k == 0 => n
    // apply to variable witnesses
    case v: Funct  => print(App(v, (1 to v.arity).map(i => witness(i-1)).toList))
    case Const(i) => i.toString
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
          OpVar(v, 
            args.map(visit(_).asInstanceOf[Var]), 
            exprs.map(visit(_))) compose visit(v).asInstanceOf[Funct]
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
  }
    
}

trait Environment extends Logger {
  // input tables
  var inputs: List[Var] = List()
  // algorithms
  var algorithms: List[Algorithm] = List()

  def addInput(v: Var) {
    inputs = v :: inputs
  }

  def addAlg(alg: Algorithm) =
    if (algorithms.contains(alg)) 
      error("adding duplicate algorithm: " + alg)
    else
      algorithms = alg :: algorithms

  import java.io.PrintStream
  def pythonize(out: PrintStream = Console.out) {
    out.println(Python.prelude)
    import Python.{print => txt}
    for (input <- inputs) {
      out.println("@memoize\ndef " + txt(input) + "(" + 
        (1 to input.arity).map("v"+_).mkString(", ") + "):")
      out.println("  return random.randint(0, 1000)")
    }
    for (alg <- algorithms)
      out.println(alg)
  }
}


/**
 * Refinement steps
 */
class Proof extends Environment {
  sealed trait Step
  case class Refine(op: Funct) extends Step
  case object Specialize extends Step
  case object Relax extends Step 

  // keep all versions of algorithms
  import collection.mutable.{ HashMap, MultiMap, Set }
  import Transform._
  val steps = new HashMap[Algorithm, Set[(Algorithm, Step)]]
    with MultiMap[Algorithm, (Algorithm, Step)]
  var COUNTER = 0

  // attempt to follow down refinement chain
  def lift(from: Var, to: Var): Option[Funct] = {
    for ((k, vs) <- steps
         if k.v == from;
         (l, s) <- vs)
        s match {
          case Refine(op) =>
            if (l.v == to)
              return Some(op)
            else lift(l.v, to) match {
              case Some(op2) => 
                return Some(op compose op2)
              case _ =>
            }
          case _ =>
        }
    return None
  }

  def step(f: Algorithm => (Algorithm, Step)): Refinement = {
    case x: Algorithm => 
      val (out, stp) = f(x)
      steps.addBinding(x, (out, stp))
      message(x.v + " refined to " + out.v)
      addAlg(out)
      //println(out)    
      COUNTER = COUNTER + 1
      out
  }
  
  // Check induction
  def induction(a: Algorithm, metric: Expr, base: Expr) {
    visit(a.expr)(a.pre, exprTransformer {
      case (path, app @ App(v, args)) if v == a.v =>
        if (! SMT.prove(path implies (metric.s(a.args zip args) < metric))) {
          error("failed induction check on " + a.v + " at " + app) 
        }
        app
    })
    
    if (! SMT.prove(a.pre implies (base <= metric)))
      error("failed base case check")
  }
  
  def $ = Var.fresh().name

  // Refinement steps

  type Refinement = Algorithm => Algorithm

  // Identity
  def id: Refinement = identity[Algorithm]

  // Substitute the body of an algorithm
  def manual(name: String, body: Expr, hint: Refinement = id) = step {
    case in @ Algorithm(v, args, pre, e) =>
      val out = Algorithm(v.rename(name), args, pre, body)
      val out1 = hint(out)
      if (! SMT.prove(pre implies (e === out1.expr))) {        
        error("failed to prove equivalence of body expressions")
        (in, Refine(v))
      } else
        (out, Refine(out.v))
  }

  // Add parameters to a function 
  def introduce(name: String, vs: Var*) = step {
    case Algorithm(v, args, pre, e) => 
      val w = Var(name, v.arity + vs.size)
      val args1 = args.map(_.fresh)
      (Algorithm(w, args ++ vs.toList, pre, e), 
       Refine(OpVar(w, args1, args1 ++ vs.toList)))        
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
      (Algorithm(w, args, pre, push(e)), Refine(w))
  }

  // Push functions down refinement chain
  def refine(name: String, from: Var, to: Var) = step {
    case Algorithm(v, args, pre, e) =>
      val w = v.rename(name)
      (Algorithm(w, args, pre, transform(e) {
        case App(u: Var, uargs) if u == from && lift(from, to).isDefined =>
          App(lift(from, to).get, uargs).flatten
      }), Refine(w))
  }

  // Specialize application of c0 to its immediate version
  // TODO check termination
  def specialize(name: String, c0: Algorithm) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      def push(path: Pred, e: Expr): Expr = 
        visit(e)(path, exprTransformer {
          case (path, App(u, uargs)) if u == c0.v =>      
            steps(c0).collect {
              case (c1, Specialize) if SMT.prove(path implies c1.pre.s(c1.args zip uargs)) => c1
            } headOption match {
              case Some(c1) => App(c1.v, uargs)
              case None => App(c0.v, uargs)
            }
        }) 
      (Algorithm(w, args, pre, push(pre, expr)), Refine(w))
  }

  // Create specialized versions of alg by splitting the domain
  def partition(name: String, base: Pred, splits: Pred*): Algorithm => List[Algorithm] = {    
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

      message(v + " refined to " + name)
      val alg = Algorithm(Var(name, v.arity), args, pre, out) 
      steps.addBinding(a, (alg, Refine(alg.v)))    
      for (alg <- algs) 
        steps.addBinding(a, (alg, Specialize))
      
      alg :: algs.reverse
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
        (Algorithm(w, args, pre, 
          visit(e)(pre, exprTransformer {
            case (path, App(w, args)) if w == ov.v && 
              proveEq(path, ov, nv, op, hint1, hint2) =>
              (App(op, args).flatten)
          })), Refine(w))
    }
  }


  var SKIP_FIRST = false
    
  // Prove by induction that pred(v) => c(v) = c(f(v)) where d = OpVar(c, f)
  def proveEq(pred: Pred, ov: Algorithm, nv: Algorithm, op: Funct, 
    hint1: Refinement, hint2: Refinement): Boolean = {
    assert (nv.v == op.v)
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
    val nind = flatten(hint2(Algorithm(nv.v, nv.args, nv.pre, 
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
      (Algorithm(w, args, pre, transform(flatten(expr)) {
        case App(w, wargs) if w == c.v =>
          c.expr.s(c.args zip wargs)
      }), Refine(w))
  }
        
  // Split "k in range(a,b)" into "k1 in range(a,e) and k2 in range(e,b)"
  def splitRange(name: String, k: Var, mid: Expr) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      (Algorithm(w, args, pre, visit(expr)(pre, seqTransformer {
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
      })), Refine(w))
  }

  // Fix a value for which old function symbol is used
  def guard(name: String, pred: Pred) = step {
    case Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      (Algorithm(w, args, pre, IF (pred -> v(args:_*)) ELSE expr), Refine(w))
  }

  // Generalize pre-condition
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
      (Algorithm(w, args, pre1, expr), Relax)
  }

  // Generalize variable application
  def genApp(name: String, ov: Var, nv: Var, which: Int = 0) = step {
    case Algorithm(v, args, pre, e) =>
      val w = Var(name, v.arity + 1)
      val args1 = args.map(_.fresh)
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
      }), Refine(OpVar(w, args1, args1 :+ (op match {
          case Some(op) => op           
          case None => nv
        }))))
    }
}

trait Unification {
  // Complete OpVar of c based on op
  import collection.mutable.ListBuffer
  def unify(c: Algorithm, op: (Var, Expr)*) {
    val map = op.toMap   
    val cvs = c.args
    // assume we are given all 0-arity variables
    // now infer remaining linear operators (including c itself)
    var operators = Map[Var, LinearOp]()
    val dvs = cvs.map { v =>
      if (map.contains(v)) 
        map(v)
      else {
        assert (v.arity > 0, "0-arity var " + v + " requires user input")
        val w = v.fresh
        w
      }
    }
    implicit val buf = new ListBuffer[Pred]
    unify(c.expr, c.expr.s(cvs zip dvs))  
    for (p <- buf)
      println(p)
  }

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

    addInput(w)
    addInput(x)
    addAlg(par)
    induction(par, j-i, 1)

    val r = Var("r", 2)
    val R = Algorithm(r, List(i, j), True, IF ((i === j-1) -> x(i)) ELSE Zero)
    val par0 = manual($, 
      Op(Reduce(c(i, k) + c(k, j) + w(i, k, j) where k in Range(i+1, j)), r(i, j)),
      unfold($, R))(par)

    val c0 = (introduce($, n, w, r) andThen 
      selfRefine("c0"))(par0)    
    val List(c1, c000, c001, c011) = partition("c1", n < 4, i < n/2, j < n/2)(c0) 
  
    val c100 = rewrite("c100", c0)(n -> n/2)(c000) 
    // use free assumption n mod 2 = 0    
    val c111 = rewrite("c111", c0)(i -> (i-n/2), j -> (j-n/2), n -> n/2, 
      w->(w>>(n/2, n/2, n/2)), 
      r->(r>>(n/2,n/2)))(c011)

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
   
    val List(b1, b000, b001, b010, b011) = partition("b1", n < 8, i < n/4, j < n/2+n/4)(b0)
       
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
    val D = Algorithm(d, List(i, j, n, w, r, s, t),
      0 <= i and i < n/2 and 0 <= j and j < n/2,
      Op(Reduce(s(i, k) + t(k, j) + w(i, k, j) where k in Range(0, n/2)), r(i, j)))
    addAlg(D)
     
    val i0 = Var("i0")
    val j0 = Var("j0")
    val i1 = Var("i1")
    val j1 = Var("j1")
    val i2 = Var("i2")
    val j2 = Var("j2")
    val bx = OpVar(b0.v, List(i1, j1), List(i1, j1, n, w, r, s, t, w1))
    // we can infer i and j displacements by looking at pre-condition of b0 and case of b000   
    val b100 = rewrite("b100", b0, splitRange($, Var("k1"), n/4), unfold($, D))(
        i->i,
        j->(j-n/4),
        n->n/2,        
        w->(w>>(0,n/4,n/4)),
        w1->(w1>>(0,0,n/4)),        
        t->(t>>(n/4,n/4)),
        r->OpVar(d, List(i0, j0), List(i0, j0-n/4, n/2, w1>>(0,n/4,n/2), 
          r>>(0,n/2),s>>(0,n/4),bx>>(n/4,n/2)))          
      )(b000)
    val b111 = rewrite("b111", b0, splitRange($, Var("k2"), n/4+n/2), unfold($, D))(
        i->(i-n/4),
        j->(j-n/2),
        s->(s>>(n/4,n/4)),
        t->(t>>(n/2,n/2)),
        w->(w>>(n/4,n/2,n/2)),
        w1->(w1>>(n/4,n/4,n/2)),
        n->n/2,
        r->OpVar(d, List(i0, j0), List(i0+n/4, j0+n/2, n/2, w>>(0,n/2,0),
          r, bx>>(0,n/2), t>>(n/2,0)))
      )(b011)
    val b101 = rewrite("b101", b0, 
        splitRange($, Var("k1"), n/4) andThen splitRange($, Var("k2"), n/4+n/2),
        unfold($, D) andThen unfold($, D))(
        j->(j-n/2),
        n->n/2,
        s->s,
        w1->(w1>>(0,0,n/2)),
        t->(t>>(n/2,n/2)),
        w->(w>>(0,n/2,n/2)),
        r->OpVar(d, List(i0, j0), List(i0, j0+n/2, n/2, w1>>(0,n/4,0),
          OpVar(d, List(i2, j2), List(i2, j2, n/2, w>>(0,n/2,0), r, bx>>(0,n/2), t>>(n/2,0))), 
          s>>(0,n/4), bx>>(n/4,0)))        
      )(b001)

    val List(d1, d00, d01, d10, d11) = partition("d1", n < 4, i < n/4, j < n/4)(D)
    val d100 = rewrite("d100", D, splitRange($, k, n/4), unfold($, D))(
      n->n/2, r->OpVar(d, List(i0, j0), List(i0,j0,n/2, 
        w>>(0,n/4,0),r,s>>(0,n/4),t>>(n/4,0)))
    )(d00)
    val d110 = rewrite("d110", D, splitRange($, k, n/4), unfold($, D))(
      i->(i-n/4), n->n/2, 
      r->OpVar(d, List(i0, j0), List(i0, j0, n/2, w>>(n/4,0,0), r>>(n/4,0), s>>(n/4,0), t)),
      w->(w>>(n/4,n/4,0)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,0))
    )(d10)
    val d101 = rewrite("d101", D, splitRange($, k, n/4), unfold($, D))(
      j->(j-n/4), n->n/2,
      r->OpVar(d, List(i0, j0), List(i0, j0, n/2, w>>(0,0,n/4), r>>(0,n/4), s, t>>(0, n/4))),
      w->(w>>(0,n/4,n/4)),
      s->(s>>(0,n/4)),
      t->(t>>(n/4,n/4))
    )(d01)
    val d111 = rewrite("d111", D, splitRange($, k, n/4), unfold($, D))(
      i->(i-n/4), j->(j-n/4), n->n/2,
      r->OpVar(d, List(i0, j0), List(i0, j0, n/2, w>>(n/4,0,n/4), r>>(n/4,n/4), s>>(n/4,0), t>>(0,n/4))),
      w->(w>>(n/4,n/4,n/4)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,n/4))
    )(d11)


    println(COUNTER + " refinements")
    pythonize()
    //GraphViz.display(steps)
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

    induction(F, k, 0)
    val a = (introduce($, n, r) andThen selfRefine("a"))(F)
    val List(a1, a000, a001, a010, a011, a100, a101, a110, a111) = partition("a1", n < 2,
        i < n/2, j < n/2, k <= n/2)(a)

    val x = (unfold($, a) andThen specialize($, a) andThen selfRefine("x"))(a000)
   
    // generalize x
    val s = Var("s", 3)
    val t = Var("t", 3)
    val b = (genApp($, x.v, s, 1) andThen selfRefine("b"))(x)
    val c = (genApp($, x.v, s, 2) andThen selfRefine("c"))(x)
    val d = (genApp($, b.v, t, 1) andThen selfRefine("d"))(b)

    // cases for b
    val List(b1, b000, b001, b010, b011, b100, b101, b110, b111) = partition("b1", n < 4, 
        i < n/4, j < n/4, k < n/4)(b)
    
    val b000x = rewrite("b000x", b)(n -> n/2)(b000)
    val b010x = rewrite("b010x", b)(
      j->(j-n/4), n->n/2, r->(r>>(0, n/4)))(b010)
    val b100x = (refine($, b.v, d.v) andThen rewrite("b100x", d)(
      i->(i-n/4), n->n/2, r->(r>>(n/4, 0)), s->(s>>(n/4,0,0))))(b100)
    val b110x = (refine($, b.v, d.v) andThen rewrite("b110x", d)(
      i->(i-n/4), j->(j-n/4), n->n/2, r->(r>>(n/4,n/4)), 
      s->(s>>(n/4,0,0)), t->(t>>(0,n/4,0))))(b110)
    val i0 = i.fresh
    val j0 = j.fresh
    SKIP_FIRST = true
    // k = n/4 should be in the first case
    val b101x = rewrite("b101x", b, guard($, k === n/4))(
      i->(i-n/4), k->(k-n/4), n->n/2, 
      s->(s>>(n/4,n/4,n/4)), 
      r->OpVar(b.v, List(i0, j0), List(i0+n/4, j0, n/4, n, r, s)))(b101)
    val b111x = rewrite("b111x", b, guard($, k === n/4))(
      i->(i-n/4), j->(j-n/4), k->(k-n/4), n->n/2,
      s->(s>>(n/4,n/4,n/4)),
      r->OpVar(b.v, List(i0, j0), List(i0+n/4, j0+n/4, n/4, n, r, s)))(b111)
    val b001x = (refine($, b.v, d.v) andThen 
      rewrite("b001x", d, guard($, k === n/4))(
      k->(k-n/4), n->n/2,
      s->(s>>(0,n/4,n/4)),
      t->(t>>(n/4,0,n/4)),
      r->OpVar(d.v, List(i0, j0), List(i0, j0, n/4, n, r, s, t))
      ))(b001)
    val b011x = (refine($, b.v, d.v) andThen
      rewrite("b011x", d, guard($, k === n/4))(
      j->(j-n/4), k->(k-n/4), n->n/2,
      s->(s>>(0,n/4,n/4)),
      t->(t>>(n/4,n/4,n/4)),
      r->OpVar(d.v, List(i0, j0), List(i0, j0+n/4, n/4, n, r, s, t))
      ))(b011)
    SKIP_FIRST = false
 
    // lift version of a
    val k0 = k.fresh
    val ax = OpVar(a.v, List(i0, j0, k0), List(i0, j0, k0, n, r))
    val amid = OpVar(a.v, List(i0, j0), List(i0, j0, n/2, n, r))

    // cases for a
    
    val a000x = rewrite("a000x", a)(n -> n/2)(a000)
    val a010x = rewrite0("a010x", a, b, a.lift(b)(ax))(
      j->(j-n/2), r->(r>>(0,n/2))
    )(a010)
    val a100x = rewrite0("a100x", a, c, a.lift(c)(ax))(
      i->(i-n/2), r->(r>>(n/2,0))
    )(a100)
    val a110x = rewrite0("a110x", a, d, a.lift(d)(ax>>(n/2,0,0), ax>>(0,n/2,0)))(
      i->(i-n/2), j->(j-n/2), r->(r>>(n/2,n/2))
    )(a110)
    SKIP_FIRST = true
    val a111x = (relax($, a.pre and i >= n/2 and j >= n/2 and k >= n/2) andThen 
      rewrite("a111x", a, guard($, k === n/2))(
        i->(i-n/2), j->(j-n/2), k->(k-n/2), n->n/2, r->(amid>>(n/2, n/2))
      ))(a111)
    val a011x = (relax($, a.pre and i < n/2 and j >= n/2 and k >= n/2) andThen
      rewrite0("a011x", a, c, a.lift(c)(ax>>(n/2,n/2,n/2)), guard($, k === n/2))(
        j->(j-n/2), k->(k-n/2), r->(amid>>(0,n/2))
      ))(a011)
    val a101x = (relax($, a.pre and i >= n/2 and j < n/2 and k >= n/2) andThen
      rewrite0("a101x", a, b, a.lift(b)(ax>>(n/2,n/2,n/2)), guard($, k === n/2))(
        i->(i-n/2), k->(k-n/2), r->(amid>>(n/2,0))
      ))(a101)
    val a001x = (relax($, a.pre and i < n/2 and j < n/2 and k >= n/2) andThen
      rewrite0("a001x", a, d, a.lift(d)(ax>>(0,n/2,n/2), ax>>(n/2,0,n/2)), guard($, k === n/2))(
        k->(k-n/2), r->amid
      ))(a001) 

    SKIP_FIRST = false 
    println(COUNTER + " refinements")
    //GraphViz.display(steps)
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
