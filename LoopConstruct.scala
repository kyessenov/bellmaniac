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

  // extract linear constraints: each linear >= 0
  def extract(p: Pred): List[Linear] = p match {
    case And(p1, p2) => extract(p1) ::: extract(p2)
    case LE(a, b) => Linear.make(b-a) :: Nil
    case LT(a, b) => Linear.make(b-a-Const(1)) :: Nil
    case GE(a, b) => Linear.make(a-b) :: Nil
    case GT(a, b) => Linear.make(a-b-Const(1)) :: Nil
    case _ => 
      error("invalid constraint: " + p)
      ???
  }

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


  // generate looping construct for first "dim" parameters of "a"
  def generate {
    // orient dependency vectors by flipping +/- coordinates so that they point
    // into lower-left corner
    val r = orient(vectors)
    println("orientation vector: " + r)

    // find iteration order and bounds
    // create fresh variables: c1 = r(c)
    val c1 = c.map(_.fresh)
    
    // formulate pre in terms of c1
    val pre1 = pre.s(c zip (r.inverse(c1)))
    
    import Linear.zero

    // get constraints
    val eqs = extract(pre1)

    // hope we're lucky and we can order c1s so that each subsequent only depends on previous    
    for (p <- c1.permutations) {              
      // compute ranges
      val ranges = 
        for (v <- p;
             pos = eqs.filter(_.proj(v) > zero);
             neg = eqs.filter(_.proj(v) < zero);
             pt = pos.map { case eq => (Const(0)-eq.drop(v).expr) / eq.proj(v).expr };
             nt = neg.map { case eq => (Const(0) - (Const(0)-eq.drop(v).expr) / eq.proj(v).expr) })
          yield Range(MAX(pt, pre1), Const(1)-MAX(nt, pre1))
      println(p) 
      println(ranges)
      return 
    }

    error("couldn't solve for loop construct")
    ???
  }
}
