object Floyd {
  import Prelude._
  import java.io.{File, PrintStream}

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
    val proof = new Proof 
    import proof._

    input(n)
    input(r)
    add(F, k)

    val a = (introduce($, n, r)(n) andThen selfRefine("a"))(F)
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
    
    // k = n/4 is the special case
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
    // relax to k >= n/2
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

    compile(F, new PrintStream(new File("floyd.py")))
    close()
  }
}

