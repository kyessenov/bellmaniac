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
  def fresh = Var.fresh(arity)
  def in(r: Range) = IntDomain(this, r)
}
object Var {
  private var counter = 0
  def fresh(arity: Int = 0) = {
    counter = counter + 1
    Var("$"+ counter)
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
  assert(v.arity == args.size && exprs.size == args.size, "wrong number of arguments in translation")
  override def arity = v.arity
  def vars = exprs.flatMap(_.vars).toSet -- args.toSet
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
  def print(alg: Algorithm): String = alg match {
    case Algorithm(v, dom, cases) => 
      "@memoize\ndef " + print(v) +
      "(" + dom.map(d => print(d.v)).mkString(", ") + "):\n" + 
      dom.collect { case d if d.pred != True  => 
        "  assert " + print(d.pred)
      }.mkString("\n") + 
      "\n  if " +
      cases.map { case (pred, expr) =>
        print(pred) + ":\n    return " + print(expr)
      }.mkString("\n  elif ")
      
  }
}

object SMT {
  val z3 = new Z3
  import z3._
  command("(declare-sort Seq 0)")
  command("(declare-fun zero () Int)")
  command("(declare-fun reduce (Seq Int) Int)")
  command("(declare-fun join (Seq Seq) Seq)")
  
  def print(e: Expr): String = e match {
    case Var(n, _) => n
    case Const(i) => i.toString
    case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
    case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
    case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
    case Div(l, r) => "(div " + print(l) + " " + print(r) + ")"
    case Zero => "zero"
    case Reduce(r, init) => "reduce(" + print(r) + ", " + init + ")"
    case _: App => ???
    case _: OpVar => ???
  }
  def print(s: Seq): String = s match {
    case Join(l, r) => "join(" + print(l) + ", " + print(r) + ")"
    case Compr(e, v, Range(l, h)) => ???
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

  // Check for satisfaction
  def check(p: Pred) = {
    push()
    for (v <- p.vars) 
      command("(declare-fun " + v.name + 
        " (" + (1 to v.arity).map(_ => "Int").mkString(" ")+ ") Int)")
    println(p)
    assert(print(p))
    val out = z3.check()
    pop()
    out
  }

  def close() {
    z3.close()
  }
}

// Recursive algorithm definition
case class Algorithm(v: Var, 
  domain: List[Domain], 
  cases: List[(Pred, Expr)]) {
  override def toString = Python.print(this)
  assert (v.arity == args.size)
  def args = domain.map(_.v)
  def pre = domain.map(_.pred).reduce(_ and _)
  def vars = 
    args.toSet ++ 
    domain.flatMap(_.pred.vars) ++ 
    cases.flatMap { case (p, e) => p.vars ++ e.vars } 

  def translate(op: (Var, Expr)*) = {
    val map = op.toMap
    val dargs = args.map(_.increment())
    val exprs = (args zip dargs).map {
      case (arg, darg) => 
        if (map.contains(arg)) 
          Transform.substitute(map(arg), args zip dargs)
        else
          darg
    }
    OpVar(v, dargs, exprs)
  }
}
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
      case App(v, args) => 
        App(transform(v).asInstanceOf[Funct], args.map(transform(_)))
      case Zero => Zero
      case Reduce(range, init) => Reduce(transform(range), transform(init))
      case OpVar(v, args, exprs) => 
        OpVar(transform(v).asInstanceOf[Var], args.map(transform(_).asInstanceOf[Var]), exprs.map(transform(_)))
    }
  def transform(s: Seq)(implicit f: PartialFunction[Expr, Expr]): Seq = 
    s match {
      case Compr(expr, v, Range(l, h)) => 
        Compr(transform(expr), transform(v).asInstanceOf[Var], 
          Range(transform(l), transform(h)))
      case Join(l, r) => Join(transform(l), transform(r))
    }

  // apply f to all expressions with a path condition
  def path(e: Expr)(implicit assumption: Pred, f: (Expr, Pred) => Unit) {
    f(e, assumption)
    e match {
      case _: Var | _: Const | Zero =>
      case e: BinaryExpr => path(e.l); path(e.r)
      case App(v, args) => path(v); args.foreach(path(_))
      case OpVar(v, args, exprs) => path(v); args.foreach(path(_)); exprs.foreach(path(_))
      case Reduce(range, init) => path(init); path(range)
    }
  }

  def path(s: Seq)(implicit assumption: Pred, f: (Expr, Pred) => Unit) {
    s match {
      case Join(a, b) => path(a); path(b)
      case Compr(e, v, Range(l, h)) => 
        path(l); path(h);
        path(e)(assumption and l <= v and v < h, f);
    }
  }

  def path(a: Algorithm)(implicit assumption: Pred, f: (Expr, Pred) => Unit) {
    a.cases.foreach {
      case (p, e) => path(e)(assumption and a.pre and p, f)
    }
  }

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
  def pushVars(vs: Var*): Algorithm => Algorithm = {
    case Algorithm(av, dom, cases) =>
      val fresh = av.increment(av.arity + vs.size)
      implicit def t: PartialFunction[Expr, Expr] = {
        case App(v, args) if v == av => App(fresh, args ::: vs.toList)
      }
      Algorithm(fresh, dom ::: vs.toList.map(Any(_)), cases.map { 
          case (pred, expr) => (transform(pred), transform(expr))
      }) 
  }
  
  def split(base: Pred, splits: (Var, Expr)*): Algorithm => Algorithm = {
    case Algorithm(av, dom, cases) =>
      val fresh = av.increment(av.arity)

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
      
      val out = Algorithm(fresh, dom, 
        (base, App(av, dom.map(_.v))) :: parts.reverse)

      out
  }

  def eliminate: Algorithm => Algorithm = {
    case a @ Algorithm(av, dom, cases) =>
      Algorithm(av.increment(), dom, cases.filter {
          case (pred, _) => SMT.check(a.pre and pred)
      })        
  }


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
  def rewrite(c: Algorithm, op: (Var, Expr)*): Algorithm => Algorithm = {    
    case Algorithm(v, dom, cases) =>
      val d = c.translate(op: _*)
      Algorithm(v.increment(), dom, cases.map {
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
    if (SMT.check(pred and c.pre and ! substitute(c.pre, 
      c.args zip App(d, c.args).flatten.args))) {
      println("*** failed domain check")
      return false
    }

    // check that inductive calls satisfy pred
    path(c)(pred, 
      (e, path) => e match {
        case a @ App(v, args) if v == c.v =>
          if (SMT.check(path and ! substitute(pred, c.args zip args))) {
            println("*** failed inductive step check")
            return false
          }
        case _ =>
      })
   
    // prove by induction on v
    // inductive step
    // ind is an uninterpreted version of c for the inductive step
    val ind = Var("$ind", c.v.arity)
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


/*
  // d is applied to f(c_args)
  // f provides map from arguments of d to expressions of c
  def unify(p: Pred, c: Algorithm, d: Algorithm, subs: (Var, Expr)*) = {
    val f = new Unification(c, d, subs: _*)
    
    try {
      // recover f, assuming both c and d are well-defined (induction holds)
      f.unify
      
      // check for well-definedness of d
      val domains = p and c.pre and ! f.unified(d.pre)
      if (SMT.check(domains)) {
        println("failed to check domains")
        None
      } else {
      
        // check for base cases and validity of inductive steps
     
        // p and base 

        // p and ! base 

        // TODO: induction proof
        Some(f)
      }
    } catch {
      case Contradiction => 
        println(f)
        None
      case _: NotImplementedError => 
        println(f)
        None
    }
  }
*/
}
/*
object Contradiction extends RuntimeException
class Unification(val C: Algorithm, val D: Algorithm, var subs: Map[Var, Expr]) {
  var vars = D.vars
  import Transform.substitute

  val hole = Var("??")

  def this(C: Algorithm, D: Algorithm, subs: (Var, Expr)*) =
    this(C, D, subs.toMap) 

  def mask = {
    var out = subs
    for (v <- vars if ! out.contains(v))
      out = out + (v -> hole)
    out
  }

  def resolved(de: Expr) = ! unified(de).vars.contains(hole)
  def resolved(dp: Pred) = ! unified(dp).vars.contains(hole)
  def unified(de: Expr) = substitute(de, mask)
  def unified(dp: Pred) = substitute(dp, mask)

  def unify() {
    if (C.cases.size != D.cases.size)
      throw Contradiction
    else
      for (((cp, ce), (dp, de)) <- C.cases zip D.cases) {
        unify(cp, dp)
        unify(ce, de)
      }
  }

  def unify(c: Expr, d: Expr) {
    println(c + " :: " + d)
    (c, d) match {
      // inductive recursive call
      case (App(cv, cargs), App(dv, dargs)) if cv == C.v && dv == D.v =>  
        // avoid inversing f, commuting diagram  
        for ((formal, actual) <- D.args zip dargs) {
          val da = unified(actual)
          val dc = substitute(mask(formal), C.args zip cargs)
          if (da != dc && SMT.check(! (da === dc)))
            throw Contradiction          
        }
      case (App(cv, cargs), App(dv, dargs)) =>
        unified(dv) match {
          // unfold lambdas in app (note lambda operator is unified as well)
          case OpVar(v, args, exprs) if resolved(dv) && v == cv =>
            for ((ca, da) <- cargs zip exprs)
              unify(ca, substitute(da, (args zip dargs).toMap))            
          case _ =>          
            unify(cv, dv)
            for ((ca, da) <- cargs zip dargs)
              unify(ca, da)      
        }
      case (Reduce(cr, ci), Reduce(dr, di)) if ci == unified(di) =>
        unify(cr, dr) 
      case (c, d: Var) if vars.contains(d) && ! subs.contains(d) =>       
        subs = subs + (d -> c)
      case (_, d) if resolved(d) =>
        // prove expression equivalence
        if (c != unified(d) && SMT.check(! (c === unified(d))))
          throw Contradiction
      case (c: BinaryExpr, d: BinaryExpr) if c.getClass == d.getClass =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case _ =>
        throw Contradiction
    }
  }

  def unify(c: Seq, d: Seq) {
    println(c + " :: " + d)
    (c, d) match {
      case (Join(c0, c1), Join(d0, d1)) =>
        unify(c0, d0)
        unify(c1, d1)
      case (Range(cl, ch), Range(dl, dh)) =>
        unify(cl, dl)
        unify(ch, dh)
      case (Compr(cexpr, cv, Range(cl, ch)), Compr(dexpr, dv, Range(dl, dh))) =>
        unify(ch - cl, dh - dl)
        unify(cv - cl + unified(dl), dv)
        unify(cexpr, dexpr)
      case (Compr(cexpr, cv, cr), Compr(dexpr, dv, dr)) =>
        unify(cr, dr)
        unify(cv, dv)
        unify(cexpr, dexpr)
      case _ =>
        throw Contradiction
    }
  }

  def unify(c: Pred, d: Pred) {
    (c, d) match {
      case (_, d) if resolved(d) =>
        // prove predicate equivalence
        if (SMT.check(c and ! unified(d)))
          throw Contradiction        
      case (c: BinaryPred, d: BinaryPred) if c.getClass == d.getClass =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case (Not(c), Not(d)) => 
        unify(c, d)
      case (c: Comparison, d: Comparison) if c.getClass == d.getClass =>
        unify(c.l, d.l)
        unify(c.r, d.r)
      case _ =>
        throw Contradiction
    }
  }

  override def toString = mask.toString
}
*/

object Parenthesis {
  implicit def int2expr(i: Int) = Const(i)

  val i = Var("i")
  val j = Var("j")  
  val c = Var("c", 2)
  val k = Var("k")

  val w = Var("w", 3)
  val x = Var("x", 1)
  val n = Var("n")
  val C = new Algorithm(c, 
    List(
      i in Range(0, n), 
      j in Range(i+1, n)
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

    val C1 = split(n < 4, i -> n/2, j -> n/2)(C0)
    println(C1)

    val C2 = eliminate(C1)
    println(C2)

    val C3 = rewrite(C0, n -> n/2)(C2)
    println(C3)

    /*
    println(unify(i >= n/2 and j >= n/2, C0, C0, 
      i -> (i-n/2), j -> (j-n/2), n -> n/2,
      x -> OpVar(x, List(j), List(j+n)),
      w -> OpVar(w, List(i, k1, j), List(i+n, k1+n, j+n))))
    */
    SMT.close()
  }
}
