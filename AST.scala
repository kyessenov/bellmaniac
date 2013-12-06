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
  def /(that: Expr) = (this, that) match {
    case (e, Const(1)) => e
    case _ => Div(this, that)
  }
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
  assert (cases.size > 0, "must have at least one case")
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
// Monadic operations
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
  assert(v.arity > 0, "must be a function " + v)
  assert(v.arity == exprs.size, "wrong number of arguments in translation " + this)
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
    case Const(i) => if (i >= 0) i.toString else "(-" + (-i).toString + ")"
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
      case (pred, expr) :: rest => "(" + print(expr) + " if " + print(pred) + " else " + (rest match {
          case Nil => print(default)
          case _ => print(Cond(rest, default))
        }) + ")"
      case _ => ???
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
zero = pow(10, 16)
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
      if (Vars(l).isEmpty || ! Vars(r).isEmpty)
        error("can't assume divisibility of " + Div(l,r))
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
      case (p, e) :: rest=> "(ite " + print(p) + " " + print(e) + "\n " + {
        rest match {
          case Nil => print(d)
          case _ => print(Cond(rest, d)) 
        }} + ")"
      case _ => ???
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

    // plus is commutative and associative
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

    assert(! prove(False) && prove(True), "over constraining check")
  }

  def close() {
    z3.close()
  }
}


object Transform {
  // path is the path condition
  // stack is local variables (from input of the transformer)
  trait Transformer {
    def apply(path: Pred, stack: List[Var], p: Pred): Option[Pred] = None
    def apply(path: Pred, stack: List[Var], e: Expr): Option[Expr] = None
    def apply(path: Pred, stack: List[Var], s: Seq): Option[Seq] = None
  }

  def visit(p: Pred)(implicit path: Pred, stack: List[Var], f: Transformer): Pred = 
    f(path, stack, p) match {
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
  
  def visit(e: Expr)(implicit path: Pred, stack: List[Var], f: Transformer): Expr = {
    f(path, stack, e) match {
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
            args.map(visit(_)(path, args ::: stack, f).asInstanceOf[Var]), 
            exprs.map(visit(_)(path, args ::: stack, f)))
        case Cond(cases, default) => 
          var els: Pred = path
          Cond(cases.map {
            case (p, e) => 
              val out = (visit(p)(els, stack, f), visit(e)(els and p, stack, f))
              els = els and !p
              out
          }, visit(default)(els, stack, f))
      }
    }
  }
  
  def visit(s: Seq)(implicit path: Pred, stack: List[Var], f: Transformer): Seq = 
    f(path, stack, s) match {
      case Some(out) => out
      case None => s match {
        case Compr(expr, v, Range(l, h)) => 
          Compr(visit(expr)(path and l <= v and v < h, v :: stack, f), 
            visit(v)(path, v :: stack, f).asInstanceOf[Var], 
            Range(visit(l), visit(h)))
        case Join(l, r) => Join(visit(l), visit(r))
        case Singleton(e) => Singleton(visit(e))
      }
    }

  // transformers

  def transformer(f: PartialFunction[Term, Term]) = new Transformer {
    override def apply(path: Pred, stk: List[Var], p: Pred) = 
      f.lift(p).asInstanceOf[Option[Pred]]
    override def apply(path: Pred, stk: List[Var], e: Expr) = 
      f.lift(e).asInstanceOf[Option[Expr]]
    override def apply(path: Pred, stk: List[Var], s: Seq) = 
      f.lift(s).asInstanceOf[Option[Seq]]
  }

  def exprTransformer(f: PartialFunction[(Pred, List[Var], Expr), Expr]) = new Transformer {
    override def apply(path: Pred, stack: List[Var], e: Expr) = f.lift(path, stack, e) 
  }  

  def predTransformer(f: PartialFunction[(Pred, List[Var], Pred), Pred]) = new Transformer {
    override def apply(path: Pred, stack: List[Var], p: Pred) = f.lift(path, stack, p)
  }

  def seqTransformer(f: PartialFunction[(Pred, List[Var], Seq), Seq]) = new Transformer {
    override def apply(path: Pred, stack: List[Var], s: Seq) = f.lift(path, stack, s)
  }

  def transform(a: Algorithm)(f: PartialFunction[(Pred, List[Var], Expr), Expr]): Expr = 
    transform(a, exprTransformer(f))

  def transform(a: Algorithm, f: Transformer): Expr = 
    visit(flatten(a.expr))(a.pre, a.args, f)
  
  def transform(e: Expr)(f: PartialFunction[Term, Term]): Expr = 
    transform(e, transformer(f))

  def transform(e: Expr, f: Transformer): Expr = 
    visit(e)(True, Nil, f)

  def transform(p: Pred)(f: PartialFunction[Term, Term]): Pred = 
    transform(p, transformer(f))

  def transform(p: Pred, f: Transformer): Pred = 
    visit(p)(True, Nil, f)
  
  def transform(s: Seq)(f: PartialFunction[Term, Term]): Seq = 
    transform(s, transformer(f))

  def transform(s: Seq, f: Transformer): Seq = 
    visit(s)(True, Nil, f)

  def substitution(f: Map[Var, Expr]) = exprTransformer {
    case (_, s, v: Var) if f.contains(v) && ! s.contains(v) => f(v) 
  }

  def substitute(e: Expr, f: Map[Var, Expr]): Expr = transform(e, substitution(f))

  def substitute(p: Pred, f: Map[Var, Expr]): Pred = transform(p, substitution(f))

  def flatten(e: Expr): Expr = transform(e) {
    case a: App => a.flatten match {
      case App(v, args) => App(v, args.map(flatten(_)))
    }
    case op: OpVar => op.flatten match {
      case OpVar(v, args, exprs) => OpVar(v, args, exprs.map(flatten(_)))
    }
  }
}


// Program environment
trait Environment extends Logger {
  // all input tables
  var inputs: List[Input] = List()
  
  // all algorithms
  var algorithms: List[Algorithm] = List()

  // termination metrics for algorithms
  var metrics: List[(Algorithm, Metric)] = Nil

  // refinement chains (v, op, w refining v) where 
  // op.v = w so that v(args) = op(args)
  var refines: List[(Algorithm, Funct, Algorithm)] = Nil

  // restrictions (v, w with stronger pre-condition) 
  var restricts: List[(Algorithm, Algorithm)] = Nil

  def input(v: Var) {
    inputs = Input(v) :: inputs
  }

  // Check for soundness of an algorithm before adding to environment
  def validate(a: Algorithm)
  
  // Add an algorithm together with termination metric
  // Metric must decrease with each recursive call, must be non-negative
  def add(a: Algorithm, m: Expr) =
    algorithms.find(_.v == a.v) match {
      case Some(a0) if a != a0 =>
        error("conflicting algorithms:\n " + a + "\n" + a0)
      case None =>
        algorithms = a :: algorithms
        metrics = (a, Metric(metrics.size, m)) :: metrics        
        validate(a)
      case _ =>
    }

  // Follow down refinement chain
  // Must be distinct values
  def concretize(from: Var, to: Var): Option[Funct] = {
    for ((k, op, l) <- refines
        if k.v == from) 
      if (l.v == to)
        return Some(op)
      else concretize(l.v, to) match {
        case Some(op2) => 
          return Some(op compose op2)
        case _ =>
      }            
    return None
  }

  def metric(c: Computation) = metrics.find(_._1 == c) match {
    case Some((_, m)) => m
    case _ => Metric.DEFAULT
  }
  
  // Induction metric: version, expression (that must be >= 0)
  case class Metric(g: Int, e: Expr) {          
    def mayCall(path: Pred, that: Metric): Boolean =       
      if (that.g > this.g) 
        false
      else if (this.g == that.g && 
              ! SMT.prove(path implies that.e < this.e)) 
        false
      else
        true
  }  
  
  object Metric {
    val DEFAULT = Metric(0, Const(0))
    def apply(app: App): Metric = app.flatten match {
      case App(v: Var, args) => algorithms.find(_.v == v) match {
        case Some(a) => metric(a) match {
          case Metric(g, e) => Metric(g, e.s(a.args zip args))
        }
        case None => DEFAULT
      }
      case _ => ???
    }      
  }

  type Refinement = Algorithm => Algorithm

  // Add a refinement step
  def step0(f: Algorithm => (Algorithm, Funct, Expr)): Refinement = { 
    (in: Algorithm) => {    
      val (out, stp, expr) = f(in)
        
      // add default metric if the algorithm is not in the environment
      add(in, metric(in).e)
      add(out, expr)
      refines = (in, stp, out) :: refines
      println(in.v + " refined to " + out.v)

      out
    }
  }

  def step(f: Refinement): Refinement = step0 { 
    (in: Algorithm) => 
      val out = f(in); 
      (out, out.v, metric(in).e) 
  }

  // Show the program state graphically
  def showGraph() {
    GraphViz.display { 
      refines.map(s => (s._1, s._2.toString, s._3)) ::: 
      restricts.map(s => (s._1, "?split", s._2))
    }
  }

  def showCallGraph() {
    GraphViz.display {
      for (a <- algorithms;
           v <- Vars(a.expr);
           b <- algorithms if b.v == v)
         yield (a.v.name, "", b.v.name)
    }
  }

  override def toString = 
    "algorithms: " + algorithms.map(_.v).mkString(", ") + "\n" +
    "inputs: " + inputs.map(_.v).mkString(", ") + "\n" +
    "metrics: " + metrics.map { case (a, m) => a.v + ":" + m }.mkString(", ")
}

// Refinement steps
class Proof extends Environment with Lowering {
  import Transform._

  def $ = Var.fresh().name 
  def $$ = new Proof { override def validate(a: Algorithm) {} }

  case class PreFailure(t: Term) extends RuntimeException  
  case class NonTermination(s: String) extends RuntimeException

  override def validate(a: Algorithm) {
    welldefined(a, metric(a), true)
  }
      
  def welldefined(a: Algorithm, m: Metric, err: Boolean = false): Boolean = { 
    try {
      welldefined(flatten(a.expr), a.pre, a.args)(0, Set(), m)     
      if (! SMT.prove(a.pre implies m.e >= Const(0)))
        throw NonTermination("can't prove base termination: " + a)
      true
    } catch {
      case PreFailure(t) => 
        if (err) error("pre-condition violation at " + t + " in " + a.v)
        false
      case NonTermination(s) => 
        if (err) error(s + " in " + a.v)
        false
    }
  }

  // maximum number of unfoldings in the well definedness check
  val MAX_UNFOLD = 5
  val CHECK_PRE = true
  val CHECK_TERMINATION = true

  // TODO: we can actually infer conditions on parameters to input functions and then check
  // pre-conditions for those
  // Algorithm: given metric, find all Apps; 
  // 1) check metric decreasing 2) find specs on parameter applications 
  // 3) recurse on applying to those parameters
  // We might have to walk up refinement chain to avoid solving fixed-point equations on 
  // calls to other algorithms

  // unfold only applications containing OpVars
  private def mustUnfold(e: Expr): Boolean = {
    transform(e) { case _: OpVar => return true }
    return false
  }

  // Rename 0-arity Vars consistently
  // Assume visiting order is unique
  private def structure(e: Expr): Expr = {
    var i = 0
    transform(e) { case v: Var if v.arity == 0 => i = i + 1; Var("$" + i) }    
  }
    
  private def welldefined(e: Expr, path: Pred, s: List[Var])
    (implicit unfolded: Int, cache: Set[Expr], m: Metric) {
    visit(e)(path, s, exprTransformer {
      case (path, s, app @ App(v: Var, vargs)) =>
        if (! s.contains(v) && ! inputs.exists(_.v == v)) {
          algorithms.find(_.v == v) match {
            case Some(a) =>             
              // check for pre-condition
              if (CHECK_PRE && ! SMT.prove(path implies a.pre.s(a.args zip vargs))) 
                throw PreFailure(app)
            
              // check for termination
              val m2 = Metric(app)
              if (CHECK_TERMINATION && ! m.mayCall(path, m2))
                throw NonTermination(s"non-decreasing metric at $app of $m2 from $m")

              // unfold to reach OpVars
              val sapp = structure(app)
              if (unfolded < MAX_UNFOLD && ! cache.contains(sapp) && mustUnfold(app)) {
                welldefined(flatten(a.expr.s(a.args zip vargs)), path, s)(
                  unfolded + 1, cache + sapp, m)              
              }
            case _ => 
              error("unknown var: " + v)
          } 
        }

        for (arg <- vargs) 
          welldefined(arg, path, s)
        
        Havoc
    })    
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
      // add 0-arity vs to metric
      val m = vs.filter(_.arity == 0).fold(metric(a).e)(_ + _)
      (Algorithm(w, args ++ vs.toList, pre, e), a.lift(w)(vs.toList:_*), m)
  }

  // Push self-application down the refinement chain
  def selfRefine(name: String) = step {
    case Algorithm(v, args, pre, e) =>
      val w = v.rename(name)        
      def push(e: Expr): Expr = transform(e) {
        case App(u: Var, uargs) if concretize(u, v).isDefined =>
          // TODO: hack around not reusing parameters from "this"
          // App(lift(u, v).get compose w, uargs.map(push(_))).flatten
          // assumes lifts can only add parameters
          App(w, uargs.map(push(_)) ++ args.drop(uargs.size))
      }
      Algorithm(w, args, pre, push(e))
  }

  // Push functions down refinement chain
  def refine(name: String, from: Var, to: Var) = step {
    case Algorithm(v, args, pre, e) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, transform(e) {
        case App(u: Var, uargs) if u == from && concretize(from, to).isDefined =>
          App(concretize(from, to).get, uargs).flatten
      })
  }

  // Specialize each application of c0 to its immediate version
  def specialize(name: String, c0: Algorithm) = step {
    case in @ Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)

      var out = Algorithm(w, args, pre, expr)
      var which = 0     
      var proceed = true

      while (proceed) {
        restricts.toStream
        .collect { case (a, c1) if a == c0 => c1 }
        .map { case c1 =>
          var i = - 1      
          Algorithm(w, args, pre, transform(out.expr) {
            case u: Var if u == c0.v => 
              i = i + 1
              if (i == which) 
                c1.v
              else
                c0.v
        }) }
        .filter(welldefined(_, metric(in)))
        .headOption match {
          case None =>  
            // none are well defined; skip over
            which = which + 1
          case Some(out2) if out2 == out =>
            // no more occurrences of c0.v
            proceed = false
          case Some(out2) =>
            // successful replacement
            out = out2
        }
      }
        
      if (out.expr == in.expr)
        error("can't specialize")
      out
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
     
      // update environment (first split algs to check well-definedness)

      for (a0 <- algs) {
        add(a0, metric(a).e)
        restricts = (a, a0) :: restricts
      }

      add(alg, metric(a).e)
      refines = (a, alg.v, alg) :: refines

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
      case in @ Algorithm(v, args, pre, e) =>
        val w = v.rename(name)
        Algorithm(w, args, pre, 
          transform(in) {
            case (path, _, App(w, args)) if w == ov.v && 
              inductiveProof(path, ov, nv, op, hint1, hint2) =>
              (App(op, args).flatten)
          })
    }
  }

  // CONTROLS FOR THEOREM PROVER
  var SKIP_FIRST = false
    
  // Prove by induction that pred(v) => c(v) = c(f(v)) where d = OpVar(c, f)
  private def inductiveProof(pred: Pred, ov: Algorithm, nv: Algorithm, op: Funct, 
    hint1: Refinement, hint2: Refinement): Boolean = {
    // check domains: d is well defined for substitution
    val domain = (pred and ov.pre) implies nv.pre.s(nv.args zip App(op, ov.args).flatten.args)
    if (! SMT.prove(domain)) {
      error("failed domain check")
      return false
    }

    // apply proof hint and get expression
    val oalg = hint1(Algorithm(ov.v, ov.args, pred and ov.pre, ov.expr))

    // prove by induction on v (c's metric)
    // inductive step
    var skip = SKIP_FIRST
    val oind = flatten(transform(oalg) {
      case (path, _, app @ App(v, args)) if v == ov.v => 
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
    })
    val nind = flatten(hint2(Algorithm(nv.v, nv.args, pred and nv.pre, 
      nv.expr.s(nv.args zip App(op, ov.args).flatten.args))).expr)
  
    if (! SMT.prove((pred and ov.pre) implies (oind === nind))) {
      message("pred")
      println(pred)
      message("goal expression")
      println(oind)
      message("derived expression")
      println(nind)
      error("failed to prove equation equality")
      return false
    }
   
    return true
  }

  // Unroll application to c
  def unfold(name: String, c: Algorithm) = step {
    case in @ Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, transform(in) {
        case (path, _, App(w, wargs)) if w == c.v =>
          c.expr.s(c.args zip wargs)
      })
  }
        
  // Split "k in range(a,b)" into "k1 in range(a,e) and k2 in range(e,b)"
  def splitRange(name: String, k: Var, mid: Expr) = step {
    case in @ Algorithm(v, args, pre, expr) =>
      val w = v.rename(name)
      Algorithm(w, args, pre, transform(in, seqTransformer {
        case (path, _, compr @ Compr(e, v, Range(l, h))) if v == k => 
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
      }), metric(a).e)
    }
}

trait Lowering extends Environment {
  // Compilation
  import java.io.PrintStream
  import Transform._

  def leaves: List[Algorithm] = 
    algorithms.filter { a => ! refines.exists(_._1 == a) }

  // Push down algorithms down the refinement chain to the leafs
  // Resulting set contains "main" and concretized algorithms together with specs
  // when necessary
  def refineAll(): List[Algorithm] = {
    var keep: List[Algorithm] = Nil

    def concretizeAll(path: Pred, s: List[Var], e: Expr)
    (implicit l: Algorithm): Expr = { 
      visit(e)(path, s, exprTransformer {
        case (_, _, app @ App(v: Var, vargs)) 
          if vargs == l.args && refines.exists {  
            case (a1, _, a2) => a1.v == v && a2 == l } =>
          // handle split specially
          assert(! keep.exists(_.v == v))
          keep = algorithms.find(_.v == v).get :: keep
          message("keeping " + v + " in " + l.v)
          app          
        case (path, s, v: Var) => 
          if (s.contains(v) || inputs.exists(_.v == v) || leaves.exists(_.v == v)) 
            v
          else leaves.find { a => concretize(v, a.v).isDefined } match {
            case Some(a) => 
              concretizeAll(path, s, concretize(v, a.v).get)
            case None => 
              error("can't locate leaf for " + v)
              v
          }          
      })
    }
  
    // modify bodies to refer only to leaves
    val concretized = for (l @ Algorithm(v, args, pre, e) <- leaves)  
      yield Algorithm(v, args, pre, flatten(concretizeAll(pre, args, e)(l)))

    val out = concretized ::: keep
         
    // copy all metrics but all at same generation
    val p = new Proof { override val CHECK_PRE = false }
    p.inputs = this.inputs
    p.algorithms = out
    p.metrics = 
      for (a <- out; (b, m) <- metrics if b.v == a.v)
        yield (a, p.Metric(0,m.e))
    
    // p.showCallGraph
    
    // TODO: can disable termination validation for now
    //for (a <- out) {
    //  print(a.v + " ")
    //   p.validate(a)  
    //}
    //println("checked termination")

    out
  }

  // Inline algorithms of the form: "return ..." that are not self-referential.
  // This type is generated by "split" tactic
  // Inlining maximizes chances of sharing down the road
  def inlineAll(p: List[Algorithm]) = {
    // simple programs
    val candidates = p.filter {
      _.expr match {
        case e: App => true        
        case _ => false
      }
    } 

    // don't form loops
    def cycle(a: Algorithm, visited: Set[Algorithm] = Set()): Boolean =
      if (visited.contains(a))
        true
      else
        Vars(a.expr).exists { v => 
          candidates.find(_.v == v) match {
            case None => false
            case Some(b) => cycle(b, visited + a)
          }
        }

    if (candidates.exists(cycle(_))) 
      error("cycle detected: " + candidates)
    
    def inline(e: Expr): Expr = transform(e) {
      case App(w, wargs0) =>
        assert(w.isInstanceOf[Var], "must be flattened")
        val wargs = wargs0 map inline
        candidates.find(_.v == w) match {
          case Some(c) => c.expr.s(c.args zip wargs)
          case None => App(w, wargs)
        }
      case OpVar(w, wargs, wexprs0) => 
        assert(w.isInstanceOf[Var], "must be flattened")
        val wexprs = wexprs0 map inline
        candidates.find(_.v == w) match {
          case Some(c) => c.expr match {
            case App(u, uargs) => OpVar(OpVar(u, c.args, uargs), wargs, wexprs).flatten
            case _ => ???
          }
          case None => OpVar(w, wargs, wexprs)
        }
    }

    @annotation.tailrec
    def inline1(e: Expr): Expr = {
      val e1 = inline(e)
      if (e1 == e)
        e
      else
        inline1(e1)
    }

    for (a @ Algorithm(v, args, pre, expr) <- p;
         if ! candidates.contains(a))
      yield Algorithm(v, args, pre, inline1(expr))    
  }

  // Generalize arguments by adding offsets to every argument function
  // Cannot be applied twice
  def offsettify(p: List[Algorithm]) = {    
    // STAGE ONE
    // add offsets arguments to functions

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
        }
    }    

    // add offset arguments to inputs and all applications
    val p1 = 
      for (Algorithm(v, args, pre, e) <- p;
           args1 = extended(args))                  
        yield Algorithm(Var(v.name, args1.size), args1, pre, extend(e)(args))
  
    // STAGE TWO
    // make use of offsets to eliminate OpVars
    // resulting expression contains OpVars that may only add expressions 
    // to the argument list
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

  def compile(main: Algorithm, out: PrintStream = Console.out, 
      printer: PythonPrinter = Python) {
    //showGraph()    
    println("compiling")
    val all = main :: inputs ::: offsettify(inlineAll(refineAll()))
    printer.print(all, out) 
    out.flush()
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
