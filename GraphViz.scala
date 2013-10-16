object GraphViz {
  type Graph[V, L] = collection.mutable.MultiMap[V, (V, L)]
  import java.io.{PrintStream, File}

  def clean(s: Any) = 
    s.toString.replace("\n", "\\l").replace("\"", "'") + "\\l"

  def write[V, L](g: Graph[V, L], out: PrintStream) {
    out println  "digraph tmp {";    
    out println  "  node [shape=box] "
   
    for ((from, vs) <- g;
         (to, l) <- vs)
      out.println("\"" + clean(from) + "\"->\"" + clean(to) + "\" [label=\"" + l +"\"]");
    out println "}";
  }

  private[this] def makeTempDot = {
    // write to a file
    val f = File.createTempFile("graph", ".dot");
    f.deleteOnExit;
    println("created dot file " + f.getAbsolutePath)
    f;
  }

  private[this] def executeDot(in: File) = {
    // write to a png file
    val out = File.createTempFile("graph", ".svg");
    out.deleteOnExit;
    val dot = Runtime.getRuntime.exec("dot -Tsvg -o " + out.getAbsolutePath + " " + in.getAbsolutePath);
    
    if (dot.waitFor != 0)
      println("dot failed to produce: " + out.getAbsolutePath);    
    
    out
  }

  private[this] def showDot(out: File) {
    Runtime.getRuntime.exec("eog " + out.getAbsolutePath);
  }

  def createDot[V, L](g: Graph[V, L]) = {
    val f = makeTempDot;
    val out = new PrintStream(f);
    write(g, out);
    out.flush;
    executeDot(f);
  }

  def display[V, L](g: Graph[V, L]) {
    val f = createDot(g);
    showDot(f);
  }
}

