// Rational number
case class Rational(n: Int, d: Int) {
  assert(d != 0)
  private def gcd(x: Int, y: Int): Int = {
    if (x == 0) 
      y
    else 
      if (x < 0) 
        gcd(-x, y)
      else if (y < 0) 
        -gcd(x, -y)
      else gcd(y % x, x)
  }
  private val g = gcd(n, d)
  val numer: Int = n/g
  val denom: Int = d/g
  def +(that: Rational) =
    Rational(numer * that.denom + that.numer * denom,
      denom * that.denom)
  
  def -(that: Rational) =
    Rational(numer * that.denom - that.numer * denom,
      denom * that.denom)
  
  def *(that: Rational) =
    Rational(numer * that.numer, denom * that.denom)
  
  def /(that: Rational) =
    Rational(numer * that.denom, denom * that.numer)

  def eq(that: Rational) =
    this.numer * that.denom == this.denom * that.numer

  def >(that: Rational) =
    this.numer * that.denom > this.denom * that.numer

  def <(that: Rational) =
    this.numer * that.denom < this.denom * that.numer

  def expr = 
    if (numer == 0)
      Const(0)
    else if (denom == 1)
      Const(numer)
    else
      Const(numer) / Const(denom)
}
// Rational linear combination
case class Linear(terms: Map[Var, Rational], free: Rational) {
  import Linear.{zero, one}

  def expr = 
    free.expr + 
    vars.map(v => v * proj(v).expr).fold(Const(0): Expr)(_ + _)   

  def vars = 
    (for ((v, r) <- terms;
         if (! (r eq zero)))
      yield v).toSet
  
  def proj(v: Var) =
    if (terms.contains(v))
      terms(v)
    else 
      zero

  def drop(v: Var) = 
    Linear(terms - v, free)

  def +(that: Linear) =
    Linear((this.vars ++ that.vars) map {
      v => (v, this.proj(v) + that.proj(v))} toMap, 
    this.free + that.free)

  def -(that: Linear) = 
    Linear((this.vars ++ that.vars) map {
      v => (v, this.proj(v) - that.proj(v))} toMap, 
    this.free - that.free)

  def *(i: Rational) =
    Linear(terms.mapValues(_*i), free*i)

}

object NonLinear extends RuntimeException

object Linear {
  val zero = Rational(0, 1)
  val one = Rational(1, 1)

  def make(e: Expr): Linear = e match {
    case Plus(a, b) => make(a) + make(b)
    case Minus(a, b) => make(a) - make(b)
    case Times(a, Const(i)) => make(a) * Rational(i, 1)
    case Times(Const(i), a) => make(a) * Rational(i, 1)
    case Div(a, Const(i)) => make(a) * Rational(1, i)
    case v: Var if v.arity == 0 => Linear(Map(v -> one), zero)
    case Const(i) => Linear(Map(), Rational(i, 1))
    case _ => throw NonLinear
  }

  def apply(e: Expr) = 
    try {
      Some(make(e))
    } catch {
      case NonLinear => None
    }

  // extract offsets from expressions if possible
  def offsets(op: OpVar): Option[(Var, List[Expr])] = op.flatten match {
    case OpVar(v: Var, args, exprs) if args.size == exprs.size =>
      val offsets = (exprs zip args) flatMap { case (e, arg) => Linear(e - arg) }      
      if (offsets.size == exprs.size &&
          offsets.forall { o => args.forall { arg => o.proj(arg) eq zero }})
        Some((v, offsets.map(_.expr)))
      else
        None
    case _ => None
  }
}

