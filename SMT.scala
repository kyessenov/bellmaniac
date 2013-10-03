private object UnsatException extends RuntimeException("inconsistent model")

case class SolverException(msg: String) extends RuntimeException(msg)

/** SMT-LIB2 compliant solver. */
trait Solver {
  /** Issue a command and expect success. */
  def command(s: String) {
    //println(s)
    >(s);
    val reply = <();
    if (reply != "success") 
      throw SolverException("unexpected reply: " + reply)
  }
  /** Check satisfiability. */
  def check(): Boolean = {
    >("(check-sat)"); 
    val reply = <();
    if (reply == "sat") 
      true
    else if (reply == "unsat")
      false
    else 
      throw SolverException("unexpected reply: " + reply)
  }
  /** Evaluate the term in the current model. */
  def eval(term: String): String = {>("(get-value (" + term + "))"); <<()}
  /** Assert a boolean condition. */
  def assert(s: String) = command("(assert " + s + ")")
  /** Push a context */
  def push() = command("(push)")
  /** Pop a context */
  def pop() = command("(pop)")
  /** Reset the solver */
  def reset() = command("(reset)")
  /** Terminate the solver. */
  def close()
  /** Send to solver. */ 
  protected def >(s: String)
  /** Receive a line from the solver. */
  protected def <(): String
  /** Receive a term from the solver. */
  def <<() = {
    import scala.collection.mutable
    val out = new mutable.ListBuffer[String]
    var balance = 0;
    do {
      var line = <();
      balance = balance + line.count(_ == '(') - line.count(_ == ')');
      out += line;
    } while (balance > 0)
    out.toList.mkString;
  }
}

/** Log input and output of a solver. */
trait Logging extends Solver {
  abstract override def >(s: String) {Console.out.println("> " + s); super.>(s)}
  abstract override def <() = {val s = super.<(); Console.out.println("< " + s); s}
  abstract override def close() = {super.close(); Console.out.println(this + " closed")}
}

/** Z3 version 3.2+. */
class Z3 extends Solver {
  import java.io._

  private def BINARY = Option(System.getProperty("smt.home")) match {
    case Some(path) => path
    case None => System.getProperty("user.home") + "/opt/z3/bin/z3"
  }

  private def PARAMS ="-smt2" :: "-in" :: "-nw" :: Nil

  private var process = {
    val pb = new ProcessBuilder((BINARY :: PARAMS).toArray: _*);
    pb.redirectErrorStream(true);
    pb.start;
  }

  private var input = new BufferedWriter(new OutputStreamWriter(process.getOutputStream));
  private var output = new BufferedReader(new InputStreamReader(process.getInputStream));

  override def >(s: String) = {input.write(s); input.newLine; input.flush}
  override def <() = output.readLine 

  command("(set-option :print-success true)")
  command("(set-option :produce-models true)")
  command("(set-option :elim-quantifiers true)")
  command("(set-option :ematching false)")
  
  // Disable MBQI
  // See: http://stackoverflow.com/questions/17706219/defining-a-theory-of-sets-with-z3-smt-lib2 
  command("(set-option :mbqi false)")
  command("(set-option :auto-config false)") 

  override def close() {
    input.close; 
    output.close; 
    process.destroy;
  }
}
 
