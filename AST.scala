sealed trait Term {
  def vars: Set[Var]
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
  def unary_! = Not(this)  
  override def toString = Python.print(this)
}
object True extends Pred {
  override def and(that: Pred) = that
  def vars = Set()
}
object False extends Pred {
  override def or(that: Pred) = that
  def vars = Set()
}
sealed trait Comparison extends Pred { 
  def l: Expr
  def r: Expr 
  def vars = l.vars ++ r.vars
}
case class Eq(l: Expr, r: Expr) extends Comparison
case class GT(l: Expr, r: Expr) extends Comparison
case class LT(l: Expr, r: Expr) extends Comparison
case class GE(l: Expr, r: Expr) extends Comparison
case class LE(l: Expr, r: Expr) extends Comparison
sealed trait BinaryPred extends Pred { 
  def l: Pred
  def r: Pred 
  def vars = l.vars ++ r.vars
}
case class And(l: Pred, r: Pred) extends BinaryPred
case class Or(l: Pred, r: Pred) extends BinaryPred
case class Not(p: Pred) extends Pred {
  def vars = p.vars
}

// Expression (integer)
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
}

// Integer expressions 
case class Const(i: Int) extends Expr {
  def vars = Set()
}
sealed trait BinaryExpr extends Expr { 
  assert (l.arity == 0 && r.arity == 0)
  def l: Expr
  def r: Expr 
  def vars = l.vars ++ r.vars
}
case class Plus(l: Expr, r: Expr) extends BinaryExpr
case class Minus(l: Expr, r: Expr) extends BinaryExpr
case class Times(l: Expr, r: Expr) extends BinaryExpr
case class Div(l: Expr, r: Expr) extends BinaryExpr
case class Mod(l: Expr, r: Expr) extends BinaryExpr
object Zero extends Expr {
  def vars = Set()
}
case class Reduce(range: Seq, init: Expr = Zero) extends Expr {
  def vars = range.vars ++ init.vars
}

// Function application
sealed trait Funct extends Expr {
  def apply(exprs: Expr*) = App(this, exprs.toList)
}
case class Var(name: String, override val arity: Int = 0) extends Funct {
  def vars = Set(this)
  def increment(arity: Int = arity) = Var(Var.inc(name), arity)
  def fresh = Var.fresh(name, arity)
  def in(r: Range) = r.l <= this and this < r.h

  def translate(args: List[Var], op: (Var, Expr)*) = {
    assert (arity > 0)
    val map = op.toMap
    val dargs = args.map(_.fresh)
    val exprs = (args zip dargs).map {
      case (arg, darg) => 
        if (map.contains(arg)) 
          Transform.substitute(map(arg), args zip dargs)
        else
          darg
    }
    OpVar(this, dargs, exprs)
  }
}
object Var {
  private var counter = 0
  def fresh(prefix: String = "_v", arity: Int = 0) = {
    counter = counter + 1
    Var(prefix+ counter, arity)
  }
  private def inc(name: String): String = {
    import java.util.regex._
    val p = Pattern.compile("\\d+$");
    val m = p.matcher(name);
    if (m.find()) {
      val i = m.group();
      name.substring(0, name.size - i.size) + (i.toInt + 1)
    } else {
      name + "0"
    }
  }
}
case class OpVar(v: Var, args: List[Var], exprs: List[Expr]) extends Funct {
  assert(v.arity > 0, "must be a function")
  assert(v.arity == args.size && exprs.size == args.size, "wrong number of arguments in translation")
  override def arity = v.arity
  def vars = exprs.flatMap(_.vars).toSet + v -- args.toSet
}
case class App(v: Funct, args: List[Expr]) extends Expr {
  assert(v.arity == args.size, "wrong number of arguments in app")
  def vars = args.flatMap(_.vars).toSet ++ v.vars
  def flatten = v match {
    case OpVar(v, vargs, vexprs) =>
      App(v, vexprs.map(Transform.substitute(_, vargs zip args)))
    case _ => this
  }
}
// Sequence of values to be reduced
sealed trait Seq extends Term 
case class Range(l: Expr, h: Expr) {
  def vars = l.vars ++ h.vars
}
case class Compr(expr: Expr, v: Var, r: Range) extends Seq {
  def vars = r.vars ++ expr.vars + v
}
case class Join(l: Seq, r: Seq) extends Seq {
  def vars = l.vars ++ r.vars
}

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
    case Reduce(r, init) => "reduce(plus, " + print(r) + ", " + print(init) + ")"
    case Zero => "zero"
    case OpVar(v, args, exprs) => "(lambda " + args.map(print(_)).mkString(", ") + 
      ": " + print(v) + "(" + exprs.map(print(_)).mkString(", ") + ")"
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
    "\n  if " +
    a.cases.map { case (pred, expr) =>
      print(pred) + ":\n    return " + print(expr)
    }.mkString("\n  elif ")      
  }
}

object SMT {
  val z3 = new Z3
  import z3._
  // Model comprehensions as sets
  // command("(define-sort Seq () (Array Int Bool))")
  // command("(declare-fun zero () Int)")
  // command("(declare-fun reduce (Seq Int) Int)")
  // command("(declare-fun join (Seq Seq) Seq)")
  // command("(declare-fun abstraction (Int) Seq)")
  command("(define-fun join ((a Int) (b Int)) Int (+ a b))")
  command("(declare-fun zero () Int)")
  command("(define-fun reduce ((a Int) (b Int)) Int (+ a b))")

 
  import collection.mutable.ListBuffer
  def print(e: Expr)(implicit side: ListBuffer[String]): String = e match {
    // TODO: passing higher order functions
    case Var(n, k) if k == 0 => n
    case v @ Var(n, k) if k > 0 => print(App(v, (1 to k).map(i => Var(n + "_v_" + i)).toList))
    case o @ OpVar(Var(n, k), _, _) => print(App(o, (1 to k).map(i => Var(n + "_v_" + i)).toList))
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
    case Reduce(r, init) => "(reduce " + print(r) + " " + init + ")"
    case a: App => a.flatten match {
      case App(Var(n, k), args) => "(" + n + " " + args.map(print(_)).mkString(" ") + ")"
      case _ => ???
    }
  }
  def print(s: Seq)(implicit side: ListBuffer[String]): String = s match {
    case Join(l, r) => "(join " + print(l) + " " + print(r) + ")"
    case Compr(e, v, Range(l, h)) =>
      /* TODO: not working, use dumb approximation
      val k = Var.fresh()
      side += "(declare-fun " + print(k) + " () Seq)";      
      val i = Var.fresh()      
      side += "(assert (forall ((" + print(i) + " Int)) " + 
        "(iff (select " + print(k) + " " + print(i) + ") (exists ((" + print(v) + " Int)) " +
          print(l <= v and v < h and i === e) + "))))"
      print(k)
      */
      import Transform.substitute
      print(substitute(e, Map(v->h)) - substitute(e, Map(v->l)))
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

  // Check for satisfaction
  def check(p: Pred) = {
    val side = new ListBuffer[String]
    for (v <- p.vars) {
      side += "(declare-fun " + v.name + 
        " (" + (1 to v.arity).map(_ => "Int").mkString(" ")+ ") Int)";
      // equality witnesses
      for (i <- 1 to v.arity)
        side += "(declare-fun " + v.name + "_v_" + i + " () Int)";
    }

    val formula = print(p)(side)

    push()
    for (s <- side)
      command(s)
    assert(formula)
    val out = z3.check()

    if (out) {
      println("cex: " + p)
      for (v <- p.vars if v.arity == 0)
        println(v.name + " -> " + eval(v.name))
    }

    pop()

    out
  }

  def close() {
    z3.close()
  }
}

// Recursive algorithm definition
case class Algorithm(v: Var, args: List[Var], pre: Pred, cases: List[(Pred, Expr)]) {
  override def toString = Python.print(this)
  assert (v.arity == args.size)

  def vars = 
    args.toSet ++ 
    pre.vars ++ 
    cases.flatMap { case (p, e) => p.vars ++ e.vars } 

  def excluded = {
    var els: Pred = True
    cases.map {
      case (p, e) => 
        val out = (p, els, e)
        els = els and !p
        out
    }
  }

  def translate(op: (Var, Expr)*) = v.translate(args, op: _*)
  def make(f: List[(Pred, Expr)] => List[(Pred, Expr)]) = 
    Algorithm(v.increment(), args, pre, f(cases))
}

object Transform { 
  def walk(p: Pred)(implicit f: Function2[Term, Pred, Option[Term]], path: Pred): Pred = 
    f(p, path) match {
      case Some(out) => out.asInstanceOf[Pred]
      case None => p match {
        case True => True
        case False => False
        case And(l, r) => And(walk(l), walk(r))
        case Or(l, r) => Or(walk(l), walk(r))
        case Not(l) => Not(walk(l))
        case Eq(l, r) => Eq(walk(l), walk(r))
        case LT(l, r) => LT(walk(l), walk(r))
        case GT(l, r) => GT(walk(l), walk(r))
        case LE(l, r) => LE(walk(l), walk(r))
        case GE(l, r) => GE(walk(l), walk(r))
      }
    }

  def walk(e: Expr)(implicit f: Function2[Term, Pred, Option[Term]], path: Pred): Expr = 
    f(e, path) match {
      case Some(out) => out.asInstanceOf[Expr]
      case None => e match {
        case _: Var => e
        case _: Const => e
        case Plus(l, r) => Plus(walk(l), walk(r))
        case Minus(l, r) => Minus(walk(l), walk(r))
        case Times(l, r) => Times(walk(l), walk(r))
        case Div(l, r) => Div(walk(l), walk(r))
        case Mod(l, r) => Mod(walk(l), walk(r))
        case App(v, args) => 
          App(walk(v).asInstanceOf[Funct], args.map(walk(_)))
        case Zero => Zero
        case Reduce(range, init) => Reduce(walk(range), walk(init))
        case OpVar(v, args, exprs) => 
          OpVar(walk(v).asInstanceOf[Var], args.map(walk(_).asInstanceOf[Var]), exprs.map(walk(_)))
      }
    }

  def walk(s: Seq)(implicit f: Function2[Term, Pred, Option[Term]], path: Pred): Seq = 
    f(s, path) match {
      case Some(out) => out.asInstanceOf[Seq]
      case None => s match {
        case Compr(expr, v, Range(l, h)) => 
          Compr(walk(expr)(f, path and (l <= v and v < h)), walk(v).asInstanceOf[Var], 
            Range(walk(l), walk(h)))
        case Join(l, r) => Join(walk(l), walk(r))
      }
    }

  def walk(a: Algorithm)(implicit f: Function2[Term, Pred, Option[Term]], path: Pred): List[(Pred, Expr)] = 
    a.cases.map {
      case (p, e) => (walk(p)(f, path and a.pre), walk(e)(f, path and a.pre and p))
    }      

  def transform(e: Expr)(f: PartialFunction[Term, Term]): Expr = walk(e)({
    case (te, _) if f.isDefinedAt(te) => Some(f(te))
    case _ => None    
  }, True)

  def transform(p: Pred)(f: PartialFunction[Term, Term]): Pred = walk(p)({
    case (te, _) if f.isDefinedAt(te) => Some(f(te))
    case _ => None    
  }, True)

  def transform(a: Algorithm)(f: PartialFunction[Term, Term]): List[(Pred, Expr)] = walk(a)({
    case (te, _) if f.isDefinedAt(te) => Some(f(te))
    case _ => None    
  }, True)

  def substitute(e: Expr, f: Map[Var, Expr]): Expr = 
    transform(e) {
      case v: Var if f.contains(v) => f(v)
    }

  def substitute(e: Expr, f: List[(Var, Expr)]): Expr = substitute(e, f.toMap)

  def substitute(p: Pred, f: Map[Var, Expr]): Pred =
    transform(p) {
      case v: Var if f.contains(v) => f(v)
    }
   
  def substitute(p: Pred, f: List[(Var, Expr)]): Pred = substitute(p, f.toMap)
 
  // These transformation are correct by construction
  def generalize(ds: Var*) = (a: Algorithm) => {    
    val fresh = a.v.increment(a.v.arity + ds.size)
    def t: PartialFunction[Term, Term] = {
      case App(v, args) if v == a.v => App(fresh, args ::: ds.toList)
    }
    Algorithm(fresh, a.args ::: ds.toList, a.pre, a.cases.map { 
        case (pred, expr) => (transform(pred)(t), transform(expr)(t))
    }) 
  }

  def generalizeEach(v: Var) = (a: Algorithm) => {
    var vs: List[Var] = Nil
    val cases = transform(a) {
      case w: Var if v == w => 
        val u = v.fresh
        vs = u :: vs
        u
    }
    Algorithm(a.v.increment(a.v.arity + vs.size), a.args ++ vs, a.pre, cases)
  }
  
  def split(base: Pred, splits: (Var, Expr)*) = (a: Algorithm) => {    
    // create specialized versions of alg by splitting the domain
    var parts: List[(Pred, Expr)] = Nil;
    def rec(vs: List[(Var, Expr)], prefix: Pred = True) {
      vs match {
        case Nil => parts = (prefix, App(a.v, a.args)) :: parts
        case v :: vs => 
          rec(vs, prefix and v._1 < v._2)
          rec(vs, prefix and v._1 >= v._2)
      }        
    }

    rec(splits.toList)
    
    a.make(_ => (base, App(a.v, a.args)) :: parts.reverse)
  }

  def eliminate = (a: Algorithm) =>
    a.make(_.filter {
        case (pred, _) => SMT.check(a.pre and pred)
    })        
  


/*
  Rewrite operation c(v) = d(w)
  To make it feasible, we restrict to the following form
    "p(v) => c(v) = d(f(v))"
  where f is the translation operator consisting of affine transformations,
  lift-translate transformations of the argument functions, and combination thereof.
  p is an arbitrary predicate.

  Given that c and d are defined inductively, we prove this by induction on v.
  Two main arguments:
  1) base case
  2) inductive cases v -> v1,v2,...,vk
    (some of the vi cases may not satisfy p, in which case nothing is known)

  p and c are given. d is chosen from a small set of functions. We'd like f to be inferred.

  The strategy is to use direct unification of d expression with c.
  1) Prove d recursive calls satisfy induction.
  2) Replace d calls with c calls, may need to invert f and/or apply-unapply function transformations.
  3) Unify! Later on we can use theorem proving to make SMT do the job for us but for now we need to infer f.
*/  

  // Rewrite calls to d.v as d provided it's valid
  def rewrite(c: Algorithm, op: (Var, Expr)*) = (a: Algorithm) => {
    val d = c.translate(op: _*)  
    a.make(_.map {
        case (pred, expr) => (pred, 
          if (proveInd(pred, c, d)) {
            transform(expr) {
              case App(w, args) if w == c.v => App(d, args).flatten
            }
          } else {
            expr
          })
      })      
  }

  // Prove by induction that pred(v) => c(v) = c(f(v)) where d = OpVar(c, f)
  def proveInd(pred: Pred, c: Algorithm, d: OpVar): Boolean = {
    assert (d.v == c.v)
    // check domains: d is well defined at p and c.pre
    val domain = pred and c.pre and ! substitute(c.pre, 
      c.args zip App(d, c.args).flatten.args)
    if (SMT.check(domain)) {
      println("*** failed domain check")
      return false
    }

    // check that inductive calls satisfy pred
    walk(c)({ (e, path) => 
      e match {
        case a @ App(v, args) if v == c.v =>
          if (SMT.check(path and ! substitute(pred, c.args zip args))) {
            println("*** failed inductive step check")
            return false
          }
        case _ =>
      }
    None }, pred)

   
    // prove by induction on v
    // inductive step
    // ind is an uninterpreted version of c for the inductive step
    val ind = Var("_ind_"+c.v.name, c.v.arity)
    for ((p, e) <- c.cases) {
      val ce = transform(e) {
        case App(v, args) if v == c.v =>
          // unroll with d to ind
          App(d, args).flatten match {
            case App(v, args) => assert(v == c.v); App(ind, args)
          }
      }
      val de = transform(substitute(e, c.args zip App(d, c.args).flatten.args)) {
        case App(v, args) if v == c.v => App(ind, args)
      }
      if (SMT.check(pred and c.pre and p and !(ce === de))) {
        println("*** failed to prove equation equality")
        println(ce)
        println(de)
        return false
      }
    }

    // base case
    // TODO
    true
  }


  // Replace calls to c with calls to a provided ind decreases and pre-condition is satisfied
  def refine(c: Algorithm, ind: Expr) = (a: Algorithm) => {
    val fresh = a.v.increment()
    Algorithm(fresh, a.args, a.pre, walk(a)({ (e, path) => 
      e match {          
        case app @ App(v, args) if v == c.v =>
          if (SMT.check(path and ! (substitute(ind, c.args zip args) < ind)))
            None
          else if (SMT.check(path and ! substitute(a.pre, a.args zip args)))
            None
          else
            Some(App(fresh, args))
        case _ => 
          None
      }}, True))          
  }

  // Create two algorithm: one for the specific case, another with the case replaced by itself
  def specialize(k: Int, n: String) = (a: Algorithm) => {
    var i = -1
    var b: Algorithm = a
    val a1 = a.make(_.map {
        case (p, e) => 
        i = i + 1
        if (i == k) {
          b = Algorithm(Var(n, a.v.arity), a.args, a.pre and p, List((True, e)))
          (p, b.v(a.args:_*))
        } else {
          (p, e)
        }
      })
    (a1, b)          
  }
  
  def unfold(c: Algorithm) = (a: Algorithm) =>
    a.make(_.flatMap {
        case (p, App(v, args)) if v == c.v =>
          c.cases.map {
            case (cp, ce) => (p and cp, substitute(ce, c.args zip args))
          }
        case t => List(t)
    })

  // Split "k in range(a,b) into k1 in range(a,e) and k2 in range(e,b)
  def splitRange(k: Var, mid: Expr) = (a: Algorithm) =>   
    a.make(_.map {
      case (p, e) => (p, transform(e) {
        case Compr(e, v, Range(l, h)) if v == k && 
          ! SMT.check(a.pre and ! (l <= mid and mid <= h)) => 
          val v1 = Var(v.name + "1")
          val v2 = Var(v.name + "2")
          Join(Compr(substitute(e, Map(v->v1)), v1, Range(l, mid)), 
              Compr(substitute(e, Map(v->v2)), v2, Range(mid, h)))
      })
    })
  
}

object Parenthesis {
  implicit def int2expr(i: Int) = Const(i)

  val i = Var("i")
  val j = Var("j")  
  val c = Var("c", 2)
  val k = Var("k")
  val l = Var("l")

  val w = Var("w", 3)
  val x = Var("x", 1)
  val n = Var("n")
  val C = Algorithm(c, List(i, j), 
    (i in Range(0, n)) and (j in Range(i+1, n)), 
    List(
      (i === j - 1, x(j)),
      (True, Reduce(Join(
        Compr(c(i, k) + c(k, j), k, Range(i+1, j)),
        Compr(w(i, l, j), l, Range(i+1, j))
      )))
    )
  )


  def main(args: Array[String]) {
    import Console.println
    import Transform._
    println(C)

    val c0 = generalize(n, w, x)(C)
    println(c0)

    val c1 = split(n < 4, i -> n/2, j -> n/2)(c0)
    println(c1)

    val c2 = eliminate(c1)
    println(c2)

    val c3 = rewrite(c0, n -> n/2)(c2)
    println(c3)
 
    // domain check fails for n = 3, i = 1, j = 2
    // use free assumption n mod 2 = 0
  
    val c4 = rewrite(c0, i -> (i-n/2), j -> (j-n/2), n -> n/2, 
      x -> x.translate(List(j), j->(j+n/2)), 
      w -> w.translate(List(i, j, k), i->(i+n/2), j->(j+n/2), k->(k+n/2)))(c3)
    println(c4)

    val c5 = refine(c0, n)(c4)
    println(c5)

    val (c6, b) = specialize(2, "B")(c5)
    println(c6)
    println(b)

    val b0 = unfold(c0)(b)
    println(b0)

    val b1 = splitRange(k, n/2)(b0)
    println(b1)

    val b2 = refine(c0, j-i)(b1)
    println(b2)

    val b3 = generalizeEach(c0.v)(b2)
    println(b3)

    SMT.close()
  }
}
