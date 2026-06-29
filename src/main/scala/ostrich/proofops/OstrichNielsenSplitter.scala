/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2022-2025 Matthew Hague, Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ostrich.proofops

import ostrich._

import ap.basetypes.IdealInt
import ap.parameters.Param
import ap.proof.ModelSearchProver
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.terfor.{ConstantTerm, VariableTerm, Formula, Term, TerForConvenience}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object OstrichNielsenSplitter {

  abstract class DecompPoint(
    val atom    : Atom,
    val leftLen : LinearCombination
  )

  case class SimpleDecompPoint(
    _atom   : Atom,               // Atom containing the terms
    left    : Seq[Term],          // left terms, in reverse order
    _leftLen : LinearCombination, // cumulative length of the left terms
    right   : Seq[Term]           // right terms
  ) extends DecompPoint(_atom, _leftLen)

  case class InsideLitDecompPoint(
    _atom        : Atom,               // Atom containing the terms
    left         : Seq[Term],          // left terms, in reverse order
    _leftLen      : LinearCombination, // cumulative length of the left terms
    right        : Seq[Term],          // right terms
    stringLit    : Int,                // if of the split string literal
    stringLitPos : Int                 // position at which the string literal
                                       // is split
  ) extends DecompPoint(_atom, _leftLen)

  ////////////////////////////////////////////////////////////////////////////
  // Decision-tree logger.  Every branching / normalization decision taken by
  // the Nielsen splitter records a node here; after each addition the whole
  // tree is (re)written to a JSON file so the file is always up to date even
  // if the solver is interrupted.  The output path defaults to
  // "decision_tree.json" in the working directory and can be overridden with
  // the OSTRICH_DECISION_TREE environment variable (or -Dostrich.decisionTree).
  object DecisionTreeLogger {
    import java.io.{File, PrintWriter}
    import scala.collection.mutable.ArrayBuffer

    private val path : String =
      Option(System.getenv("OSTRICH_DECISION_TREE"))
        .orElse(sys.props.get("ostrich.decisionTree"))
        .getOrElse("decision_tree.json")

    private val nodes = new ArrayBuffer[String]

    // Signature of the proof goal the next decision is taken in.  Princess
    // explores the proof tree depth-first; when it backtracks to a parent
    // goal to try another branch, that goal's signature reappears, which lets
    // the visualizer reconstruct the real branching structure from the
    // otherwise-flat decision sequence.
    @volatile var context : String = ""
    // Lazily produces the JSON array of ALL word equations present in the goal
    // the next decision is taken in.  A thunk (not an eager value) so the
    // potentially-expensive expansion runs only when a node is actually
    // logged, not on every goal the plugin visits.
    @volatile var contextEqsProvider : () => String = () => "[]"
    private var seq : Int = 0

    // Set of order-constants present in the goal the next decision is taken in.
    // Princess's order grows monotonically down each proof branch: a goal keeps
    // all of its parent's constants and each split adds its own fresh (Skolem)
    // constants.  So the parent of a decision is the previously-logged decision
    // whose constant set is the LARGEST subset of the current one — this lets us
    // recover the real parent/branch structure even though every goal has a
    // distinct gid.  Updated per goal (like `context`).
    @volatile var contextConsts : Set[String] = Set.empty

    // Per logged decision: (seq, its goal's constant set).  Used to compute the
    // parent by maximal-subset, and to assign branch indices among siblings.
    private val nodeConsts  = new ArrayBuffer[(Int, Set[String])]
    private val childCount  = new scala.collection.mutable.HashMap[Int, Int]

    def esc(s : String) : String =
      s.flatMap {
        case '"'  => "\\\""
        case '\\' => "\\\\"
        case '\n' => "\\n"
        case '\r' => "\\r"
        case '\t' => "\\t"
        case c if c < ' ' => "\\u%04x".format(c.toInt)
        case c    => c.toString
      }

    def str(s : String)      : String = "\"" + esc(s) + "\""
    def num(n : Int)         : String = n.toString
    def arr(xs : Seq[String]): String = "[" + xs.mkString(", ") + "]"
    def strArr(xs : Seq[String]) : String = arr(xs.map(str))

    /** Add one decision node. `fields` maps keys to already-JSON-encoded
      * values (use str/num/arr/strArr helpers). */
    def addNode(fields : Seq[(String, String)]) : Unit = synchronized {
      val mySeq    = seq
      val myConsts = contextConsts

      // Parent = earlier decision whose constant set is the largest subset of
      // ours (ties broken by the most recent seq).  -1 marks the root.
      var parent     = -1
      var parentSize = -1
      for ((s, cs) <- nodeConsts)
        if (cs.subsetOf(myConsts) &&
            (cs.size > parentSize || (cs.size == parentSize && s > parent))) {
          parent     = s
          parentSize = cs.size
        }
      // Branch index = order in which this parent's direct children appear.
      val branch =
        if (parent >= 0) {
          val b = childCount.getOrElse(parent, 0); childCount(parent) = b + 1; b
        } else 0

      nodeConsts += ((mySeq, myConsts))

      val tagged =
        Seq("seq" -> num(mySeq), "gid" -> str(context),
            "parentSeq" -> num(parent), "branch" -> num(branch),
            "state" -> contextEqsProvider()) ++ fields
      seq += 1
      val body = tagged.map { case (k, v) => str(k) + ": " + v }.mkString(", ")
      nodes += "{ " + body + " }"
      flush()
    }

    private def flush() : Unit =
      // Logging must never disrupt the solver: if the output file is
      // momentarily locked (antivirus / editor / mapped section), swallow the
      // I/O error instead of letting it propagate into the proof search.
      //
      // Write to a temp file and atomically rename it onto `path`, so the JSON
      // is never observed half-written: if the solver is killed (e.g. OOM)
      // mid-write, the temp file is the only casualty and `path` still holds the
      // last complete tree.  (A direct overwrite would leave a truncated record
      // and an unparseable file.)
      try {
        import java.nio.file.{Files, Paths, StandardCopyOption}
        val json =
          "{\n  \"decisionTree\": [\n    " +
            nodes.mkString(",\n    ") +
            "\n  ]\n}\n"
        val tmp = new File(path + ".tmp")
        val w = new PrintWriter(tmp)
        try w.write(json) finally w.close()
        try
          Files.move(tmp.toPath, Paths.get(path),
                     StandardCopyOption.REPLACE_EXISTING,
                     StandardCopyOption.ATOMIC_MOVE)
        catch {
          // ATOMIC_MOVE is not supported on every filesystem; fall back to a
          // plain replacing move, which is still far safer than overwriting.
          case _ : Throwable =>
            Files.move(tmp.toPath, Paths.get(path),
                       StandardCopyOption.REPLACE_EXISTING)
        }
      } catch {
        case _ : Throwable => // ignore
      }
  }

}

////////////////////////////////////////////////////////////////////////////////

class OstrichNielsenSplitter(goal : Goal,
                             theory : OstrichStringTheory,
                             flags : OFlags) {
  import theory.{_str_++, _str_len, strDatabase, StringSort}
  import OFlags.debug
  import OstrichNielsenSplitter._

  val order        = goal.order
  val X            = new ConstantTerm("X")
  val extOrder     = order extend X

  val rand         = Param.RANDOM_DATA_SOURCE(goal.settings)

  val facts        = goal.facts

  // Tag the logger with a signature of this goal, so decisions taken in the
  // same proof goal share a gid and sibling branches can be reconstructed.
  DecisionTreeLogger.context = Integer.toHexString(facts.hashCode)
  // Snapshot this goal's order-constants so the logger can recover the real
  // parent/branch of each decision by maximal-subset (orders nest down a branch).
  DecisionTreeLogger.contextConsts =
    order.orderedConstants.iterator.map(_.toString).toSet

  val predConj     = facts.predConj
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  val concatPerRes = concatLits groupBy (_(2))
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap

  // Lazily snapshot ALL word equations present in this goal (consecutive
  // concat literals sharing a result term, k-1 equations per group), expanded
  // to leaves.  Evaluated only when a decision is logged in this goal.
  DecisionTreeLogger.contextEqsProvider = () => {
    val eqs =
      (for ((res, lits) <- concatPerRes if lits.size >= 2;
            h <- 0 until (lits.size - 1))
       yield expandedSideStr(lits(h)(0))   + " . " + expandedSideStr(lits(h)(1)) +
             " == " +
             expandedSideStr(lits(h+1)(0)) + " . " + expandedSideStr(lits(h+1)(1)))
        .toSeq.distinct
    DecisionTreeLogger.strArr(eqs)
  }

  def resolveConcat(t : LinearCombination)
                  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

  // Collect all concat atoms in the subtree of a specific atom (children only).
  def concatAtomsOf(atom: Atom): Seq[Atom] =
    Seq(atom) ++
    concatPerRes.get(atom(0)).toSeq.flatMap(lits => concatAtomsOf(lits.head)) ++
    concatPerRes.get(atom(1)).toSeq.flatMap(lits => concatAtomsOf(lits.head))

  // Flatten a term into its leaf constituents by following concatPerRes (first lit only).
  def flattenTerm(t: LinearCombination): Seq[LinearCombination] =
    concatPerRes.get(t) match {
      case Some(lits) => flattenTerm(lits.head(0)) ++ flattenTerm(lits.head(1))
      case None       => Seq(t)
    }

  // Print all top-level equations (result terms not used as input elsewhere) as flat chains.
  def printFlatEquations(tag: String): Unit = {
    // val usedAsInput = concatLits.flatMap(lit => Seq(lit(0), lit(1))).toSet
    // val roots = concatPerRes.keys.filterNot(usedAsInput.contains).toSeq
    // val toPrint = if (roots.nonEmpty) roots else concatPerRes.keys.toSeq
    // for (root <- toPrint; lits <- concatPerRes.get(root); lit <- lits)
    //   Console.err.println("  " + flattenTerm(lit(0)).map(term2String).mkString(" . ") +
    //     " . " + flattenTerm(lit(1)).map(term2String).mkString(" . ") + " = " + term2String(root))
  }

  // Dump the full word-equation state of the current goal (every concat atom,
  // flattened to leaves, grouped by its result term) plus the length atoms.
  // Used to see exactly which state a (possibly non-exhaustive) split is applied
  // to, when diagnosing spurious models.
  def dumpState(tag: String): Unit = {
    Console.err.println(tag + " --- goal word equations ---")
    for ((res, lits) <- concatPerRes; lit <- lits)
      Console.err.println(tag + "   " +
        expandTerm(lit(0)).map(term2String).mkString(".") + "." +
        expandTerm(lit(1)).map(term2String).mkString(".") +
        " = " + term2String(res) + (if (lits.size >= 2) "   (eq, " + lits.size + " defs)" else ""))
    Console.err.println(tag + " --- lengths ---")
    for ((t, ln) <- lengthMap)
      Console.err.println(tag + "   len(" + term2String(t) + ") -> " + ln)
  }

  def lengthFor(t: LinearCombination): LinearCombination = {
    if (strDatabase.isConcrete(t)) {
      // Handle concrete terms
      LinearCombination((strDatabase.term2ListGet(t)).size)
    } else {
      // Handle the case where the lengthMap does not contain the term
      lengthMap.getOrElse(t, {
        if (debug) {
          Console.err.println(s"No length found for term: $t, returning zero length")
        }
        LinearCombination.ZERO
      })
    }
  }


  def eval(t           : LinearCombination,
           lengthModel : ReduceWithConjunction) : Int = {
    import TerForConvenience._
    implicit val o = extOrder

    val f = lengthModel(t === X)
    assert(f.size == 1 && f.constants == Set(X))
    (-f.head.constant).intValueSafe
  }

  def evalLengthFor(t : LinearCombination,
                    lengthModel : ReduceWithConjunction) : Int =
    eval(lengthFor(t), lengthModel)

  type ChooseSplitResult =
    (Seq[LinearCombination], // left terms
     LinearCombination,      // length of concat of left terms
     LinearCombination,      // term to split
     Seq[LinearCombination]) // right terms

  def chooseSplit(splitLit1    : Atom,
                  splitLit2    : Atom,
                  lengthModel  : ReduceWithConjunction)
                               : ChooseSplitResult = {
    val splitLenConc = evalLengthFor(splitLit2(0), lengthModel)
    chooseSplit(splitLit1, splitLenConc, lengthModel,
                List(), List(), List())
  }

  def chooseSplit(t            : LinearCombination,
                  splitLen     : Int,
                  lengthModel  : ReduceWithConjunction,
                  leftTerms    : List[LinearCombination],
                  leftLenTerms : List[LinearCombination],
                  rightTerms   : List[LinearCombination])
                               : ChooseSplitResult =
    (concatPerRes get t) match {
      case Some(lits) =>
        chooseSplit(lits.head, splitLen, lengthModel,
                    leftTerms, leftLenTerms, rightTerms)
      case None =>
        ((leftTerms.reverse,
          LinearCombination.sum(
            for (t <- leftLenTerms) yield (IdealInt.ONE, t), order),
          t, rightTerms))
    }

  def chooseSplit(lit          : Atom,
                  splitLen     : Int,
                  lengthModel  : ReduceWithConjunction,
                  leftTerms    : List[LinearCombination],
                  leftLenTerms : List[LinearCombination],
                  rightTerms   : List[LinearCombination])
                               : ChooseSplitResult = {
    val left        = lit(0)
    val right       = lit(1)
    val leftLen     = lengthFor(left)
    val leftLenConc = eval(leftLen, lengthModel)

    if (splitLen <= leftLenConc)
      chooseSplit(left, splitLen, lengthModel,
                  leftTerms, leftLenTerms, right :: rightTerms)
    else
      chooseSplit(right, splitLen - leftLenConc, lengthModel,
                  left :: leftTerms, leftLen :: leftLenTerms, rightTerms)
  }

  def splittingFormula(split     : ChooseSplitResult,
                       splitLit2 : Atom)
                                 : Conjunction = {
    val builder = new FormulaBuilder(goal, theory)

    val (leftTerms, _, symToSplit, rightTerms) = split

    val leftSplitSym, rightSplitSym = builder.newVar(StringSort)

    builder.addConcat(leftSplitSym, rightSplitSym, symToSplit)

    builder.addConcatN(leftTerms ++ List(leftSplitSym),   splitLit2(0))
    builder.addConcatN(List(rightSplitSym) ++ rightTerms, splitLit2(1))

    builder.result
  }

  def diffLengthFormula(split : ChooseSplitResult,
                        splitLit2 : Atom) : Conjunction = {
    import TerForConvenience._
    implicit val o = order

    val (_, leftTermsLen, symToSplit, _) = split
    val splitLen = lengthFor(splitLit2(0))

    (splitLen < leftTermsLen) |
    (splitLen > leftTermsLen + lengthFor(symToSplit))
  }

  /**
   * Compute all prefix/suffix pairs for the given concat term.
   */
  def decompositionPoints(lit : Atom) : Seq[SimpleDecompPoint] = {
    implicit val o = order

    val points = new ArrayBuffer[SimpleDecompPoint]

    def genPoints(t          : LinearCombination,
                  leftTerms  : List[Term],
                  len        : LinearCombination,
                  rightTerms : List[Term],
                  leftMost   : Boolean) : Unit =
      if (strDatabase isConcrete t) {
        if (!leftMost)
          points += SimpleDecompPoint(lit, leftTerms, len, t :: rightTerms)
      } else {
        (concatPerRes get t) match {
          case Some(Seq(concatLit)) => {
            genPoints(concatLit(0),
                      leftTerms,
                      len,
                      concatLit(1) :: rightTerms,
                      leftMost)
            genPoints(concatLit(1),
                      concatLit(0) :: leftTerms,
                      len + lengthFor(concatLit(0)),
                      rightTerms,
                      false)
          }
          case _ =>
            if (!leftMost)
              points += SimpleDecompPoint(lit, leftTerms, len, t :: rightTerms)
        }
      }

    genPoints(lit(0), List(),       LinearCombination.ZERO, List(lit(1)), true)
    genPoints(lit(1), List(lit(0)), lengthFor(lit(0)),      List(),       false)

    points.toSeq
  }

  /**
   * Compute all prefix/suffix pairs for the given concat term; also
   * split string literals in the term into prefix/suffix pairs.
   */
  def decompositionPointsWithLits(lit : Atom) : Seq[DecompPoint] = {
    import LinearCombination.Constant

    val rawPoints = decompositionPoints(lit)

    def splitLits(decomp : DecompPoint) : Seq[DecompPoint] = decomp match {
      case SimpleDecompPoint(atom,
                             Seq(Constant(IdealInt(strId))),
                             leftLen,
                             right) => {
        val strLen =
          strDatabase.id2List(strId).size
        val newSplits =
          for (n <- 1 until strLen)
          yield InsideLitDecompPoint(atom, List(),
                                     LinearCombination(n), right, strId, n)
        newSplits ++ List(decomp)
      }
      case SimpleDecompPoint(atom,
                             left,
                             leftLen,
                             Seq(Constant(IdealInt(strId)), right @ _*)) => {
        val strLen =
          strDatabase.id2List(strId).size
        val newSplits =
          for (n <- 1 until strLen)
          yield InsideLitDecompPoint(atom, left, leftLen + n, right, strId, n)
        List(decomp) ++ newSplits
      }
      case decomp =>
        List(decomp)
    }

    for (decomp    <- rawPoints;
         newDecomp <- splitLits(decomp))
    yield newDecomp
  }

  def concatLeft(decomp : DecompPoint)
                (implicit builder : FormulaBuilder) : Term = decomp match {
    case decomp : SimpleDecompPoint =>
      builder.concat(decomp.left.reverse)
    case decomp : InsideLitDecompPoint => {
      import decomp.{left, stringLit, stringLitPos}
      val strId =
        strDatabase.list2Id(strDatabase.id2List(stringLit).take(stringLitPos))
      builder.concat((List(LinearCombination(strId)) ++ left).reverse)
    }
  }

  def concatRight(decomp : DecompPoint)
                 (implicit builder : FormulaBuilder) : Term = decomp match {
    case decomp : SimpleDecompPoint =>
      builder.concat(decomp.right)
    case decomp : InsideLitDecompPoint => {
      import decomp.{right, stringLit, stringLitPos}
      val strId =
        strDatabase.list2Id(strDatabase.id2List(stringLit).drop(stringLitPos))
      builder.concat(List(LinearCombination(strId)) ++ right)
    }
  }

  /**
   * Decompose equations of the form a.b = c.d if it can be derived
   * that |a| = |c|.
   */
  def decompEquations : Seq[Plugin.Action] = {
    if (lengthLits.isEmpty)
      return List()

    val multiGroups =
      concatPerRes filter {
        case (res, lits) => lits.size >= 2 && !(strDatabase isConcrete res)
      }

    val decompActions =
      (for ((res, lits) <- multiGroups;
            act <- decompEquation(res, lits))
       yield act).toSeq

    decompActions
  }

  def decompEquation(resultTerm     : Term,
                     concatLiterals : Seq[Atom]) : Seq[Plugin.Action] = {
    implicit val o = order
    import TerForConvenience._

    val splitPoints = new MHashMap[Term, DecompPoint]

    val actions = new ArrayBuffer[Plugin.Action]

    for (lit <- concatLiterals) {
      val decomps = decompositionPointsWithLits(lit)

      var stop = false

      for (decomp <- decomps; if !stop) {
        import decomp.leftLen
        (splitPoints get leftLen) match {
          case Some(otherDecomp) => {
            val otherDecomp = splitPoints(leftLen)
            stop = true

            if (debug) {
              Console.err.println("Decomposing equation:")
              Console.err.println("  " +
                                  term2String(otherDecomp.atom(0)) + " . " +
                                  term2String(otherDecomp.atom(1)) + " == " +
                                  term2String(decomp.atom(0)) + " . " +
                                  term2String(decomp.atom(1)))
            }

            actions += Plugin.RemoveFacts(conj(lit))

            implicit val builder = new FormulaBuilder(goal, theory)

            val newLeft    = concatLeft (decomp)
            val newRight   = concatRight(decomp)
            val otherLeft  = concatLeft (otherDecomp)
            val otherRight = concatRight(otherDecomp)

            builder addConjunct (newLeft  === otherLeft)
            builder addConjunct (newRight === otherRight)

            DecisionTreeLogger.addNode(Seq(
              "rule"     -> DecisionTreeLogger.str("decompEquation"),
              "kind"     -> DecisionTreeLogger.str(
                              "Nielsen decomposition (a.b = c.d, |a|=|c|)"),
              // expanded form: intermediate concat variables are unfolded to
              // their leaf constituents (a.b == c.d in fully expanded shape)
              "equation" -> DecisionTreeLogger.str(
                              expandedSideStr(otherDecomp.atom(0)) + " . " +
                              expandedSideStr(otherDecomp.atom(1)) + " == " +
                              expandedSideStr(decomp.atom(0)) + " . " +
                              expandedSideStr(decomp.atom(1))),
              "equationFolded" -> DecisionTreeLogger.str(
                              term2String(otherDecomp.atom(0)) + "." +
                              term2String(otherDecomp.atom(1)) + " == " +
                              term2String(decomp.atom(0)) + "." +
                              term2String(decomp.atom(1))),
              "splitLen" -> DecisionTreeLogger.str(decomp.leftLen.toString),
              "action"   -> DecisionTreeLogger.str(
                              "Plugin.AddAxiom + Plugin.RemoveFacts"),
              "branches" -> DecisionTreeLogger.strArr(Seq(
                              expandedSideStr(newLeft)  + " = " + expandedSideStr(otherLeft),
                              expandedSideStr(newRight) + " = " + expandedSideStr(otherRight)))
            ))

            actions +=
              Plugin.AddAxiom(concatLits ++ lengthLits, // TODO: make specific
                              builder.result,
                              theory)
          }
          case None => {
            splitPoints.put(decomp.leftLen, decomp)
          }
        }
      }
    }

    actions.toSeq
  }

  /**
   * Decompose equations of the form a.b = w, in which w is some
   * concrete word.
   */
  def decompSimpleEquations : Seq[Plugin.Action] = {
    if (lengthLits.isEmpty)
      return List()

    for (lit <- concatLits;
         if strDatabase isConcrete lit.last;
         act <- decompSimpleEquation(lit))
    yield act
  }

  /**
   * Decompose one equation of the form a.b = w, in which w is some
   * concrete word.
   */
  def decompSimpleEquation(lit : Atom) : Seq[Plugin.Action] = {
    import LinearCombination.Constant
    import TerForConvenience._

    val decomps = decompositionPoints(lit)

    val constLenPoints =
      for (SimpleDecompPoint(_, left, Constant(IdealInt(len)), right) <-
           decomps.iterator)
      yield (left, len, right)

    if (constLenPoints.hasNext) {
      val (left, len, right) = constLenPoints.next

      val result       = strDatabase term2ListGet lit.last
      val resultPrefix = strDatabase.list2Id(result take len)
      val resultSuffix = strDatabase.list2Id(result drop len)

      val builder = new FormulaBuilder(goal, theory)

      builder.addConcatN(left.reverse, l(resultPrefix))
      builder.addConcatN(right,        l(resultSuffix))

      DecisionTreeLogger.addNode(Seq(
        "rule"     -> DecisionTreeLogger.str("decompSimpleEquation"),
        "kind"     -> DecisionTreeLogger.str(
                        "Nielsen decomposition (a.b = concrete word)"),
        "equation" -> DecisionTreeLogger.str(
                        left.reverse.map(term2String).mkString(".") + "." +
                        right.map(term2String).mkString(".") + " == " +
                        term2String(lit.last)),
        "splitLen" -> DecisionTreeLogger.num(len),
        "action"   -> DecisionTreeLogger.str(
                        "Plugin.AddAxiom + Plugin.RemoveFacts"),
        "branches" -> DecisionTreeLogger.strArr(Seq(
                        left.reverse.map(term2String).mkString(".") + " = " +
                          term2String(l(resultPrefix)),
                        right.map(term2String).mkString(".") + " = " +
                          term2String(l(resultSuffix))))
      ))

      List(Plugin.RemoveFacts(lit),
           Plugin.AddAxiom(concatLits ++ lengthLits, // TODO: make specific
                           builder.result,
                           theory))
    } else {
      /*
      for ((_, t :: left, len, right) <- decomps)
        if (strDatabase isConcrete t) {
          println
          println("Concrete: " + decomps)
          println
        }

      for ((_, left, len, Seq(t)) <- decomps)
        if (strDatabase isConcrete t) {
          println
          println("Concrete: " + decomps)
          println
        }
       */

      List()
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Apply the Nielsen transformation to some selected equation.
   */
  private def isCommProxy(lits: Seq[Atom]): Boolean =
    lits.size == 2 && {
      val a = lits(0); val b = lits(1)
      a(0) == b(1) && a(1) == b(0)
    }

  def splitEquation : Seq[Plugin.Action] = {
    val multiGroups =
      concatPerRes filter {
        case (res, lits) => lits.size >= 2 && !(strDatabase isConcrete res)
      }

    // Precompute comm class membership to filter out comm-defining pairs.
    val commComposites: Set[LinearCombination] = (for {
      (_, lits) <- concatPerRes; lit <- lits
      if isUngrounded(lit(0)) && isUngrounded(lit(1))
    } yield lit(2)).toSet
    val commClasses = computeCommutationClasses()
      .map(cls => cls.filter(z => !commComposites.contains(z))).filter(_.size >= 2)
    val commElemToClass = (for (cls <- commClasses; z <- cls) yield z -> cls).toMap

    def isCommDefiningPair(l1: Atom, l2: Atom): Boolean = {
      val lhs = flattenTerm(l1(0)) ++ flattenTerm(l1(1))
      val rhs = flattenTerm(l2(0)) ++ flattenTerm(l2(1))
      val cls = lhs.headOption.flatMap(h => if (isUngrounded(h)) commElemToClass.get(h) else None)
        .orElse(lhs.lastOption.flatMap(h => if (isUngrounded(h)) commElemToClass.get(h) else None))
      cls.exists { c =>
        lhs.forall(z => isUngrounded(z) && c.contains(z)) &&
        rhs.forall(z => isUngrounded(z) && c.contains(z)) &&
        lhs.sorted(Ordering.by(term2String)) == rhs.sorted(Ordering.by(term2String))
      }
    }

    val splittableTerms =
      concatLits.iterator.map(_(2)).filter(multiGroups.keySet).toList.distinct
        .filter { res =>
          val lits = multiGroups(res)
          !(lits.size == 2 && isCommDefiningPair(lits(0), lits(1)))
        }

    if (splittableTerms.isEmpty) {
      // if (concatLits.isEmpty) {
      //   Console.err.println("[splitEquation] concatLits=0, dumping all goal predicates:")
      //   for (p <- predConj.predicates)
      //     Console.err.println("  pred: " + p + " posLits=" +
      //       predConj.positiveLitsWithPred(p).size +
      //       " negLits=" + predConj.negativeLitsWithPred(p).size)
      //   Console.err.println("  arith negEqs: " + facts.arithConj.negativeEqs.size)
      //   Console.err.println("  arith posEqs: " + facts.arithConj.positiveEqs.size)
      // } else {
      //   Console.err.println("[splitEquation] splittableTerms empty")
      //   Console.err.println("  concatLits (" + concatLits.size + "):")
      //   for (lit <- concatLits)
      //     Console.err.println("    " + term2String(lit(0)) + " . " +
      //                         term2String(lit(1)) + " = " + term2String(lit(2)))
      //   Console.err.println("  multiGroups (result terms with 2+ lits):")
      //   for ((res, lits) <- multiGroups)
      //     Console.err.println("    " + term2String(res) + " -> " + lits.size + " lits")
      // }
      return List()
    }

    val termToSplit = splittableTerms(rand nextInt splittableTerms.size)
    val literals    = multiGroups(termToSplit)

    val splitLit1   = literals(rand nextInt literals.size)
    val splitLit2   = (literals filterNot (_ == splitLit1))(
                        rand nextInt (literals.size - 1))

    if (lengthLits.isEmpty) {
      Console.err.println(
        "Warning: Nielsen transformation is currently only enabled" +
          " in combination with option -length=on.")
      List()
    } else {
      Console.err.println("[splitEquation] current equations:")
      printFlatEquations("[splitEquation]")
      // Normalize via commutation classes before splitting (thesis §3.4/§3.5);
      // falls through to the plain Nielsen split when no normalization applies
      // or when the commutation extension is disabled.
      splitEquationWithLenNorm(splitLit1, splitLit2, multiGroups.size)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * TODO: this needs more work, currently not used!
   */
  private def splitEquationNoLen(splitLit1 : Atom, splitLit2 : Atom,
                                 multiGroupNum : Int)
                                                 : Seq[Plugin.Action] = {

    import TerForConvenience._
    implicit val o = order

    val split1 = (List(),
                  null,
                  splitLit1(0), List(splitLit1(1)))
    val split2 = (List(splitLit1(0)),
                  null,
                  splitLit1(1), List())

    if (debug) {
      Console.err.println(
        "Applying Nielsen transformation (# word equations: " + multiGroupNum +
          ")")
      Console.err.println("  " +
                          term2String(splitLit1(0)) + " . " +
                          term2String(splitLit1(1)) + " == " +
                          term2String(splitLit2(0)) + " . " +
                          term2String(splitLit2(1)))
    }

    val nil = strDatabase.str2Id("")

    val zeroCases =
      List(
        (conj(splitLit2(0) === nil), List()),
        (conj(splitLit2(0) =/= nil, splitLit2(1) === nil), List())
      )

    val splitCases =
      for (split <- List(split1, split2)) yield {
        (splittingFormula(split, splitLit2) &
           splitLit2(0) =/= nil & splitLit2(1) =/= nil,
         List(Plugin.RemoveFacts(Conjunction.conj(splitLit2, order))))
      }

    List(
      Plugin.AxiomSplit(concatLits,
                        zeroCases ++
                          (if (rand.nextBoolean) splitCases else splitCases.reverse),
                        theory))
  }

  //////////////////////////////////////////////////////////////////////////////

  // Normalize splitLit1/splitLit2 via comm classes before splitting.
  // If the flattened lhs/rhs of both lits start (or end) with variables from
  // the same comm class, rewrite them to canonical order and return AddAxiom +
  // RemoveFacts instead of an AxiomSplit.  Falls through to splitEquationWithLen
  // when no normalization is possible.
  private def splitEquationWithLenNorm(splitLit1 : Atom, splitLit2 : Atom,
                                       multiGroupNum : Int)
                                                      : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val o = order

    val rawClasses = computeCommutationClasses()
    if (flags.commutation && rawClasses.nonEmpty) {
      val composites: Set[LinearCombination] = (for {
        (res, lits) <- concatPerRes
        lit         <- lits
        a = lit(0); b = lit(1)
        if isUngrounded(a) && isUngrounded(b)
      } yield res).toSet
      val knownClasses = rawClasses.map(cls => cls.filter(z => !composites.contains(z)))
                                   .filter(_.size >= 2)
      val elemToClass  = (for (cls <- knownClasses; z <- cls) yield z -> cls).toMap

      val lhse = flattenTerm(splitLit1(0)) ++ flattenTerm(splitLit1(1))
      val rhse = flattenTerm(splitLit2(0)) ++ flattenTerm(splitLit2(1))
      val res  = splitLit1(2)

      // find comm class shared by both prefix heads (or suffix tails)
      val pfxCls = lhse.headOption
        .flatMap(h => if (isUngrounded(h)) elemToClass.get(h) else None)
        .filter(cls => rhse.headOption.exists(h => isUngrounded(h) && cls.contains(h)))
      val sfxCls = if (pfxCls.isEmpty) lhse.lastOption
        .flatMap(h => if (isUngrounded(h)) elemToClass.get(h) else None)
        .filter(cls => rhse.lastOption.exists(h => isUngrounded(h) && cls.contains(h)))
      else None

      // A commutation class shared at the prefix heads or the suffix tails.
      val cls0 = pfxCls.orElse(sfxCls)

      for (cls <- cls0) {
        // Skip equations that purely define commutativity: both sides consist
        // only of class variables and are permutations of each other.
        val lhsAllInCls = lhse.forall(z => isUngrounded(z) && cls.contains(z))
        val rhsAllInCls = rhse.forall(z => isUngrounded(z) && cls.contains(z))
        val isCommDef   = lhsAllInCls && rhsAllInCls &&
                          lhse.sorted(Ordering.by(term2String)) ==
                          rhse.sorted(Ordering.by(term2String))
        if (isCommDef) {
          Console.err.println("[splitEquation-norm] skip comm-defining equation: " +
            lhse.map(term2String).mkString(" ") + " == " + rhse.map(term2String).mkString(" "))
        } else {
          // Canonically reorder the leaf zones and cancel the common commutation
          // block at BOTH ends:  res = P1 · res' · P2,  remD == remO == res'.
          val (p1, p2, remD, remO) = cancelBothEnds(lhse, rhse, cls)
          val cancelled = p1.nonEmpty || p2.nonEmpty

          if ((cancelled && remD.nonEmpty && remO.nonEmpty) ||
              remD != lhse || remO != rhse) {
            val doCancel = remD.nonEmpty && remO.nonEmpty
            val normFormula = {
              val builder = new FormulaBuilder(goal, theory)
              if (doCancel) {
                val resMid = builder.newVar(StringSort)
                val pChain : Seq[Term] =
                  p1.map(z => z : Term) ++ Seq(resMid : Term) ++ p2.map(z => z : Term)
                builder.addConcatN(pChain, res)   // res = P1 · res' · P2
                builder.addConcatN(remD, resMid)  // remD == res'
                builder.addConcatN(remO, resMid)  // remO == res'
              } else {
                if (remD.nonEmpty) builder.addConcatN(remD, res)
                if (remO.nonEmpty) builder.addConcatN(remO, res)
              }
              builder.result
            }
            def fmt(s: Seq[LinearCombination]) = s.map(term2String).mkString(" ")
            Console.err.println("[splitEquation-norm] normalize+cancel (class={" +
              cls.map(term2String).mkString(", ") + "}" +
              (if (p1.nonEmpty) ", Pprefix=" + fmt(p1) else "") +
              (if (p2.nonEmpty) ", Psuffix=" + fmt(p2) else "") + ")")
            Console.err.println("  before: " + fmt(lhse) + "  ==  " + fmt(rhse))
            Console.err.println("  after:  " + fmt(remD) + "  ==  " + fmt(remO))

            DecisionTreeLogger.addNode(Seq(
              "rule"             -> DecisionTreeLogger.str("splitEquationWithLenNorm"),
              "kind"             -> DecisionTreeLogger.str(
                                      "commutation-class normalization + cancel (both ends)"),
              "commutationClass" -> DecisionTreeLogger.strArr(
                                      cls.toSeq.map(term2String)),
              "action"           -> DecisionTreeLogger.str(
                                      "Plugin.AddAxiom + Plugin.RemoveFacts"),
              "before"           -> DecisionTreeLogger.str(fmt(lhse) + " == " + fmt(rhse)),
              "after"            -> DecisionTreeLogger.str(fmt(remD) + " == " + fmt(remO))
            ))
            // Remove only the two top-level concat atoms forming this equation;
            // their child atoms may be shared with other equations and survive.
            return List(
              Plugin.AddAxiom(concatLits ++ lengthLits, normFormula, theory),
              Plugin.RemoveFacts(Conjunction.conj(List(splitLit1, splitLit2), order))
            )
          }
        }
      }
    }

    splitEquationWithLen(splitLit1, splitLit2, multiGroupNum)
  }

  private def splitEquationWithLen(splitLit1 : Atom, splitLit2 : Atom,
                                   multiGroupNum : Int)
                                                  : Seq[Plugin.Action] = {
    val lengthModel =
      ModelSearchProver(Conjunction.negate(facts.arithConj, order), order)

    if (lengthModel.isFalse)
      return List(Plugin.AddAxiom(List(facts.arithConj), Conjunction.FALSE, theory))

    val lengthRed =
      ReduceWithConjunction(lengthModel, extOrder)

/*
    for (t <-
    (for (lit <- concatLits.iterator;
          t <- lit.iterator;
          if !t.isConstant)
     yield t).toSet[LinearCombination].toList.sortBy(_.toString)) {
      Console.err.println("  |" + t + "| = " + evalLengthFor(t, lengthRed))
    }
*/
    val zeroSyms = for (t <- (splitLit2 take 2).iterator;
                        if evalLengthFor(t, lengthRed) == 0)
                   yield t

    if (zeroSyms.hasNext) {
      val zeroSym = zeroSyms.next
      if (debug)
        Console.err.println("Assuming " + zeroSym + " = \"\"")

      DecisionTreeLogger.addNode(Seq(
        "rule"     -> DecisionTreeLogger.str("splitEquationWithLen"),
        "kind"     -> DecisionTreeLogger.str("zero-length assumption"),
        "symbol"   -> DecisionTreeLogger.str(term2String(zeroSym)),
        "action"   -> DecisionTreeLogger.str("Plugin.AxiomSplit (2-way)"),
        "branches" -> DecisionTreeLogger.strArr(Seq(
                        term2String(zeroSym) + " = \"\"",
                        "len(" + term2String(zeroSym) + ") > 0"))
      ))

      import TerForConvenience._
      implicit val o = order
      List(
        Plugin.AxiomSplit(List(),
                          List((zeroSym === strDatabase.str2Id(""), List()),
                               (lengthFor(zeroSym) > 0,             List())),
                          theory)
      )
    } else {
      val split    = chooseSplit(splitLit1, splitLit2, lengthRed)
      val splitSym = split._3

      if (debug) {
        Console.err.println(
          "Applying Nielsen transformation (# word equations: " + multiGroupNum +
            "), splitting " + term2String(splitSym))
        Console.err.println("  " +
                            term2String(splitLit1(0)) + " . " +
                            term2String(splitLit1(1)) + " == " +
                            term2String(splitLit2(0)) + " . " +
                            term2String(splitLit2(1)))
      }

      val f1 = splittingFormula(split, splitLit2)
      val f2 = diffLengthFormula(split, splitLit2)

      Console.err.println("[Nielsen-split] standard split on " + term2String(splitSym))
      Console.err.println("  lit1: " + term2String(splitLit1(0)) + " . " + term2String(splitLit1(1)) +
                          " = " + term2String(splitLit1(2)))
      Console.err.println("  lit2: " + term2String(splitLit2(0)) + " . " + term2String(splitLit2(1)) +
                          " = " + term2String(splitLit2(2)))
      Console.err.println("  branch1 (align): " + f1)
      Console.err.println("  branch2 (diff-len): " + f2)

      // Concise, equation-level description of the two branches (the raw
      // f1/f2 Presburger formulas are huge and unreadable in the tree).
      val (lTerms, _, symTS, rTerms) = split
      val lStr = lTerms.map(term2String)
      val rStr = rTerms.map(term2String)
      val symS = term2String(symTS)
      val alignDesc =
        "align: split " + symS + "=L.R;  " +
        (lStr ++ List("L")).mkString(".") + " = " + term2String(splitLit2(0)) +
        ";  " +
        (List("R") ++ rStr).mkString(".") + " = " + term2String(splitLit2(1))
      val diffDesc =
        "diff-len: |" + term2String(splitLit2(0)) + "| outside [|" +
        (if (lStr.isEmpty) "" else lStr.mkString(".")) + "|, |" +
        (if (lStr.isEmpty) "" else lStr.mkString(".") + ".") + symS + "|]"

      DecisionTreeLogger.addNode(Seq(
        "rule"     -> DecisionTreeLogger.str("splitEquationWithLen"),
        "kind"     -> DecisionTreeLogger.str("standard Nielsen split"),
        "splitSym" -> DecisionTreeLogger.str(symS),
        "equation" -> DecisionTreeLogger.str(
                        term2String(splitLit1(0)) + "." + term2String(splitLit1(1)) +
                        " == " +
                        term2String(splitLit2(0)) + "." + term2String(splitLit2(1))),
        "lit1"     -> DecisionTreeLogger.str(
                        term2String(splitLit1(0)) + " . " + term2String(splitLit1(1)) +
                        " = " + term2String(splitLit1(2))),
        "lit2"     -> DecisionTreeLogger.str(
                        term2String(splitLit2(0)) + " . " + term2String(splitLit2(1)) +
                        " = " + term2String(splitLit2(2))),
        "action"   -> DecisionTreeLogger.str("Plugin.AxiomSplit (2-way)"),
        "branches" -> DecisionTreeLogger.strArr(Seq(alignDesc, diffDesc))
      ))

      List(
        Plugin.AxiomSplit(concatLits ++ lengthLits, // TODO: make specific
                          List((f1,
                                List(Plugin.RemoveFacts(
                                       Conjunction.conj(splitLit2, order)))),
                               (f2, List())),
                          theory)
      )
    }
  }

  private def term2String(t : Term) =
    (strDatabase term2Str t) match {
      case Some(str) => "\"" + str + "\""
      case None => t.toString
    }

  private def expandTerm(t: LinearCombination): Seq[LinearCombination] = {
    if (strDatabase isConcrete t) {
      List(t)
    } else {
      concatPerRes.get(t) match {
        case Some(lits) if lits.size == 1 =>
          expandTerm(lits.head(0)) ++ expandTerm(lits.head(1))
        case _ =>
          List(t)
      }
    }
  }

  private def expandedSideStr(t: LinearCombination): String =
    expandTerm(t).map(term2String).mkString(" . ")

  private def isNonTerminal(t: LinearCombination): Boolean =
    !(strDatabase isConcrete t) && (concatPerRes contains t)

  // Any non-concrete term (user variable OR intermediate concat result)
  private def isUngrounded(t: LinearCombination): Boolean =
    !(strDatabase isConcrete t)

  // Returns non-concrete terms that appear at least twice in the first 2 positions
  private def doubledPrefix(seq: Seq[LinearCombination]): Set[LinearCombination] = {
    val pfx = seq.take(2)
    pfx.filter(t => isUngrounded(t) && pfx.count(_ == t) >= 2).toSet
  }

  // Returns non-concrete terms that appear at least twice in the last 2 positions
  private def doubledSuffix(seq: Seq[LinearCombination]): Set[LinearCombination] = {
    val sfx = seq.takeRight(2)
    sfx.filter(t => isUngrounded(t) && sfx.count(_ == t) >= 2).toSet
  }

  private def prefixNonTerms(seq: Seq[LinearCombination]): Set[LinearCombination] =
    seq.take(2).filter(isUngrounded).toSet

  private def suffixNonTerms(seq: Seq[LinearCombination]): Set[LinearCombination] =
    seq.takeRight(2).filter(isUngrounded).toSet

  /**
   * Finds word equations matching pattern a.a... == b.a... or ...a.a == ...a.b.
   * Returns (l1, l2, res, lhs, rhs, sharedPrefix, sharedSuffix).
   */
  def findEquationsWithPrefixSuffixShared()
      : Seq[(Atom, Atom, LinearCombination,
             Seq[LinearCombination], Seq[LinearCombination],
             Set[LinearCombination], Set[LinearCombination])] = {
    val result = new ArrayBuffer[(Atom, Atom, LinearCombination,
                                  Seq[LinearCombination], Seq[LinearCombination],
                                  Set[LinearCombination], Set[LinearCombination])]

    for ((res, lits) <- concatPerRes; if lits.size >= 2) {
      for (i <- lits.indices; j <- (i + 1) until lits.size) {
        val l1  = lits(i)
        val l2  = lits(j)
        val lhs = expandTerm(l1(0)) ++ expandTerm(l1(1))
        val rhs = expandTerm(l2(0)) ++ expandTerm(l2(1))

        val lhsFirstIsNT = lhs.nonEmpty && isUngrounded(lhs.head)
        val rhsFirstIsNT = rhs.nonEmpty && isUngrounded(rhs.head)
        val lhsLastIsNT  = lhs.nonEmpty && isUngrounded(lhs.last)
        val rhsLastIsNT  = rhs.nonEmpty && isUngrounded(rhs.last)

        // a.a... == b.a... : doubled in one prefix, other side also starts with DIFFERENT non-terminal.
        // Exclude x1==x2 (same term on both sides) — that is standard prefix cancellation,
        // not commutativity, and must be handled by the regular Nielsen splitter.
        val sharedPrefixSame =
          (if (rhsFirstIsNT) (doubledPrefix(lhs) intersect prefixNonTerms(rhs))
                               .filter(x1 => rhs.headOption.exists(_ != x1))
           else Set.empty[LinearCombination]) ++
          (if (lhsFirstIsNT) (doubledPrefix(rhs) intersect prefixNonTerms(lhs))
                               .filter(x1 => lhs.headOption.exists(_ != x1))
           else Set.empty[LinearCombination])

        // x^I... == y^J... : both sides start with DIFFERENT doubled non-terminals
        val sharedPrefixCross =
          if (sharedPrefixSame.isEmpty &&
              lhsFirstIsNT && rhsFirstIsNT &&
              doubledPrefix(lhs).nonEmpty && doubledPrefix(rhs).nonEmpty)
            doubledPrefix(lhs)  // x1 from lhs; x2 = rhs.head will be found in extractPattern
          else Set.empty[LinearCombination]

        val sharedPrefix = sharedPrefixSame ++ sharedPrefixCross

        // ...a.a == ...a.b : doubled in one suffix, other side also ends with DIFFERENT non-terminal.
        val sharedSuffixSame =
          (if (rhsLastIsNT) (doubledSuffix(lhs) intersect suffixNonTerms(rhs))
                              .filter(x1 => rhs.lastOption.exists(_ != x1))
           else Set.empty[LinearCombination]) ++
          (if (lhsLastIsNT) (doubledSuffix(rhs) intersect suffixNonTerms(lhs))
                              .filter(x1 => lhs.lastOption.exists(_ != x1))
           else Set.empty[LinearCombination])

        // x^I... == y^J... suffix variant
        val sharedSuffixCross =
          if (sharedSuffixSame.isEmpty &&
              lhsLastIsNT && rhsLastIsNT &&
              doubledSuffix(lhs).nonEmpty && doubledSuffix(rhs).nonEmpty)
            doubledSuffix(lhs)
          else Set.empty[LinearCombination]

        val sharedSuffix = sharedSuffixSame ++ sharedSuffixCross

        if (sharedPrefix.nonEmpty || sharedSuffix.nonEmpty)
          result += ((l1, l2, res, lhs, rhs, sharedPrefix, sharedSuffix))
      }
    }

    result.toSeq
  }

  // Union-Find helpers
  private def ufFind(parent: MHashMap[LinearCombination, LinearCombination],
                     x: LinearCombination): LinearCombination = {
    if (!parent.contains(x)) parent(x) = x
    if (parent(x) == x) x
    else {
      val root = ufFind(parent, parent(x))
      parent(x) = root
      root
    }
  }

  private def ufUnion(parent: MHashMap[LinearCombination, LinearCombination],
                      x: LinearCombination, y: LinearCombination): Unit = {
    val rx = ufFind(parent, x)
    val ry = ufFind(parent, y)
    if (rx != ry) parent(rx) = ry
  }

  // Detects the Lemma 1 shape (thesis §3.2):
  //   s1 = x^J · y · …,   s2 = y^I · x · …    with x != y, I,J >= 1, both
  // non-terminals.  Only in this full shape is x·y = y·x implied, so this is
  // the sound trigger for adding {x,y} to a commutation class.
  private def lemma1Pair(s1 : Seq[LinearCombination],
                         s2 : Seq[LinearCombination])
      : Option[(LinearCombination, LinearCombination)] = {
    if (s1.isEmpty || s2.isEmpty) return None
    val x = s1.head
    val y = s2.head
    if (!isUngrounded(x) || !isUngrounded(y) || x == y) return None
    val jRun = s1.iterator.takeWhile(_ == x).length   // leading x's in s1
    val iRun = s2.iterator.takeWhile(_ == y).length   // leading y's in s2
    if (jRun >= 1 && iRun >= 1 &&
        (s1.lift(jRun) contains y) &&   // element right after the x-run is y
        (s2.lift(iRun) contains x))     // element right after the y-run is x
      Some((x, y))
    else
      None
  }

  def computeCommutationClasses()
      : Seq[Set[LinearCombination]] = {
    val parent = new MHashMap[LinearCombination, LinearCombination]()

    for ((res, lits) <- concatPerRes; if lits.size >= 2) {
      for (i <- lits.indices; j <- (i + 1) until lits.size) {
        val l1  = lits(i)
        val l2  = lits(j)
        val lhs = expandTerm(l1(0)) ++ expandTerm(l1(1))
        val rhs = expandTerm(l2(0)) ++ expandTerm(l2(1))

        val lhsFirstIsNT = lhs.nonEmpty && isUngrounded(lhs.head)
        val rhsFirstIsNT = rhs.nonEmpty && isUngrounded(rhs.head)

        // Sound commutativity detection following Lemma 1 (thesis §3.2):
        //   x^J · y · Φ1 = y^I · x · Φ2   (x != y, I,J >= 1)  =>  x·y = y·x
        // The whole shape must be checked, not just a doubled prefix: matching
        // only "a.a... == b.a..." unions variables that need not commute, which
        // makes the subsequent normalization rewrite subgoals incorrectly and
        // diverts the proof search (observed as a regression on testOst3).
        for ((a, b) <- lemma1Pair(lhs, rhs)) ufUnion(parent, a, b)
        for ((a, b) <- lemma1Pair(rhs, lhs)) ufUnion(parent, a, b)

        // binary commutativity encoding: a.b = t  and  b.a = t  =>  a commutes with b
        // (added by the comm branch of AxiomSplit; recognized here to prevent re-splitting)
        if (lhs.size == 2 && rhs.size == 2 &&
            lhsFirstIsNT && rhsFirstIsNT &&
            lhs(0) == rhs(1) && lhs(1) == rhs(0))
          ufUnion(parent, lhs(0), lhs(1))
      }
    }

    // group by root, keep only classes with 2+ members
    val groups = new MHashMap[LinearCombination, Set[LinearCombination]]()
    for (x <- parent.keys) {
      val root = ufFind(parent, x)
      groups(root) = groups.getOrElse(root, Set.empty) + x
    }
    groups.values.filter(_.size >= 2).toSeq
  }

  // Length of maximal prefix of seq whose elements all belong to cls
  private def prefixLenInClass(seq: Seq[LinearCombination],
                                cls: Set[LinearCombination]): Int =
    seq.indexWhere(!cls.contains(_)) match {
      case -1 => seq.length
      case n  => n
    }

  // Length of maximal suffix of seq whose elements all belong to cls
  private def suffixLenInClass(seq: Seq[LinearCombination],
                                cls: Set[LinearCombination]): Int =
    seq.reverseIterator.indexWhere(!cls.contains(_)) match {
      case -1 => seq.length
      case n  => n
    }

  // Count class elements in the prefix leaf zone only
  private def leafZoneCountsPrefix(seq: Seq[LinearCombination],
                                    cls: Set[LinearCombination])
      : Map[LinearCombination, Int] = {
    val zone = seq.take(prefixLenInClass(seq, cls))
    zone.groupBy(identity).map { case (k, v) => k -> v.size }.withDefaultValue(0)
  }

  // Count class elements in the suffix leaf zone only
  private def leafZoneCountsSuffix(seq: Seq[LinearCombination],
                                    cls: Set[LinearCombination])
      : Map[LinearCombination, Int] = {
    val zone = seq.takeRight(suffixLenInClass(seq, cls))
    zone.groupBy(identity).map { case (k, v) => k -> v.size }.withDefaultValue(0)
  }

  // Everything after the prefix leaf zone (used as U'/V' in prefix normalization)
  private def nonLeafTail(seq: Seq[LinearCombination],
                           cls: Set[LinearCombination]): Seq[LinearCombination] =
    seq.drop(prefixLenInClass(seq, cls))

  // Everything before the suffix leaf zone (used as U'/V' in suffix normalization)
  private def nonLeafHead(seq: Seq[LinearCombination],
                           cls: Set[LinearCombination]): Seq[LinearCombination] = {
    val pfxLen   = prefixLenInClass(seq, cls)
    val sfxLen   = suffixLenInClass(seq, cls)
    val sfxStart = seq.length - sfxLen
    if (pfxLen >= sfxStart) Seq.empty  // whole seq is leaf zone
    else seq.dropRight(sfxLen)
  }

  // isSuffix=false → prefix form: P . RL . U' == P . RR . V'
  // isSuffix=true  → suffix form: U' . RL . P == V' . RR . P
  def normalizeWithCommutationClass(lhs      : Seq[LinearCombination],
                                    rhs      : Seq[LinearCombination],
                                    cls      : Set[LinearCombination],
                                    isSuffix : Boolean) : Unit = {
    val nuL = if (isSuffix) leafZoneCountsSuffix(lhs, cls) else leafZoneCountsPrefix(lhs, cls)
    val nuR = if (isSuffix) leafZoneCountsSuffix(rhs, cls) else leafZoneCountsPrefix(rhs, cls)

    val mz = cls.map(z => z -> math.min(nuL(z), nuR(z))).toMap

    // Sort by m(z) descending, ties broken lexicographically
    val sortedC = cls.toSeq.sortBy(z => (-mz(z), term2String(z)))

    val P  = sortedC.flatMap(z => Seq.fill(mz(z))(z))
    val RL = sortedC.flatMap(z => Seq.fill(nuL(z) - mz(z))(z))
    val RR = sortedC.flatMap(z => Seq.fill(nuR(z) - mz(z))(z))

    val uPrime = if (isSuffix) nonLeafHead(lhs, cls) else nonLeafTail(lhs, cls)
    val vPrime = if (isSuffix) nonLeafHead(rhs, cls) else nonLeafTail(rhs, cls)

    def fmt(s: Seq[LinearCombination]) = s.map(term2String).mkString(" . ")

    val label = if (isSuffix) "Suffix-norm" else "Prefix-norm"
    Console.err.println("  " + label + " (class {" + cls.map(term2String).mkString(", ") + "}):")
    if (P.nonEmpty)  Console.err.println("    P  = " + fmt(P))
    if (RL.nonEmpty) Console.err.println("    RL = " + fmt(RL))
    if (RR.nonEmpty) Console.err.println("    RR = " + fmt(RR))
    if (isSuffix)
      Console.err.println("    " + fmt(uPrime ++ RL ++ P) + " == " + fmt(vPrime ++ RR ++ P))
    else
      Console.err.println("    " + fmt(P ++ RL ++ uPrime) + " == " + fmt(P ++ RR ++ vPrime))
  }

  // Returns normalized forms for both sides:
  // prefix: (P.RL.U',  P.RR.V')
  // suffix: (U'.RL.P,  V'.RR.P)
  private def normalizedSeqBoth(doubledSide : Seq[LinearCombination],
                                 otherSide   : Seq[LinearCombination],
                                 cls         : Set[LinearCombination],
                                 isSuffix    : Boolean)
      : (Seq[LinearCombination], Seq[LinearCombination]) = {
    val nuL = if (isSuffix) leafZoneCountsSuffix(doubledSide, cls)
              else           leafZoneCountsPrefix(doubledSide, cls)
    val nuR = if (isSuffix) leafZoneCountsSuffix(otherSide, cls)
              else           leafZoneCountsPrefix(otherSide, cls)
    val mz      = cls.map(z => z -> math.min(nuL(z), nuR(z))).toMap
    val sortedC = cls.toSeq.sortBy(z => (-mz(z), term2String(z)))
    val P   = sortedC.flatMap(z => Seq.fill(mz(z))(z))
    val RL  = sortedC.flatMap(z => Seq.fill(nuL(z) - mz(z))(z))
    val RR  = sortedC.flatMap(z => Seq.fill(nuR(z) - mz(z))(z))
    val uPr = if (isSuffix) nonLeafHead(doubledSide, cls) else nonLeafTail(doubledSide, cls)
    val vPr = if (isSuffix) nonLeafHead(otherSide, cls)   else nonLeafTail(otherSide, cls)
    val normDoubled = if (isSuffix) uPr ++ RL ++ P else P ++ RL ++ uPr
    val normOther   = if (isSuffix) vPr ++ RR ++ P else P ++ RR ++ vPr
    Console.err.println("[normalizedSeqBoth] P=" + P.map(term2String).mkString(".") +
      "  RL=" + RL.map(term2String).mkString(".") +
      "  RR=" + RR.map(term2String).mkString("."))
    Console.err.println("  normD: " + normDoubled.map(term2String).mkString("."))
    Console.err.println("  normO: " + normOther.map(term2String).mkString("."))
    (normDoubled, normOther)
  }

  // Like normalizedSeqBoth, but returns the common leaf block P SEPARATELY from
  // the two remainders, so the caller can cancel P explicitly:
  //   prefix:  P·RL·U' == P·RR·V'   →   (P, RL·U', RR·V')
  //   suffix:  U'·RL·P == V'·RR·P   →   (P, U'·RL, V'·RR)
  // Since P is the same token sequence on both sides (built from min(νL,νR) per
  // class variable, in the same canonical order), cancelling it is sound once the
  // class variables are known to commute.
  private def cancelledSeqBoth(doubledSide : Seq[LinearCombination],
                               otherSide   : Seq[LinearCombination],
                               cls         : Set[LinearCombination],
                               isSuffix    : Boolean)
      : (Seq[LinearCombination],   // common block P
         Seq[LinearCombination],   // remainder of doubled side (no P)
         Seq[LinearCombination]) = {
    val nuL = if (isSuffix) leafZoneCountsSuffix(doubledSide, cls)
              else           leafZoneCountsPrefix(doubledSide, cls)
    val nuR = if (isSuffix) leafZoneCountsSuffix(otherSide, cls)
              else           leafZoneCountsPrefix(otherSide, cls)
    val mz      = cls.map(z => z -> math.min(nuL(z), nuR(z))).toMap
    val sortedC = cls.toSeq.sortBy(z => (-mz(z), term2String(z)))
    val P   = sortedC.flatMap(z => Seq.fill(mz(z))(z))
    val RL  = sortedC.flatMap(z => Seq.fill(nuL(z) - mz(z))(z))
    val RR  = sortedC.flatMap(z => Seq.fill(nuR(z) - mz(z))(z))
    val uPr = if (isSuffix) nonLeafHead(doubledSide, cls) else nonLeafTail(doubledSide, cls)
    val vPr = if (isSuffix) nonLeafHead(otherSide, cls)   else nonLeafTail(otherSide, cls)
    val remD = if (isSuffix) uPr ++ RL else RL ++ uPr   // remainder WITHOUT P
    val remO = if (isSuffix) vPr ++ RR else RR ++ vPr
    (P, remD, remO)
  }

  // Cancel the common commutation block at BOTH ends: first the prefix block P1,
  // then the suffix block P2 of the prefix-cancelled remainders.  Returns
  // (P1, P2, remD, remO); the original equation factors as
  //     res = P1 · res' · P2   with   remD == remO == res'.
  private def cancelBothEnds(lhs : Seq[LinearCombination],
                             rhs : Seq[LinearCombination],
                             cls : Set[LinearCombination])
      : (Seq[LinearCombination], Seq[LinearCombination],
         Seq[LinearCombination], Seq[LinearCombination]) = {
    val (p1, d1, o1) = cancelledSeqBoth(lhs, rhs, cls, isSuffix = false)
    val (p2, d2, o2) = cancelledSeqBoth(d1, o1, cls, isSuffix = true)
    (p1, p2, d2, o2)
  }

  // Extract (x1, x2, doubledSide, otherSide, atomToRemove, isSuffix) from one equation.
  private def extractCommPattern(
      l1e : Atom, l2e : Atom,
      lhse: Seq[LinearCombination], rhse: Seq[LinearCombination],
      sharedPfxe: Set[LinearCombination],
      sharedSfxe: Set[LinearCombination])
      : Option[(LinearCombination, LinearCombination,
                Seq[LinearCombination], Seq[LinearCombination], Atom, Boolean)] = {
    if (sharedPfxe.nonEmpty) {
      val x1e = sharedPfxe.head
      val (ds, os, ato) =
        if (doubledPrefix(lhse).contains(x1e)) (lhse, rhse, l2e)
        else                                    (rhse, lhse, l1e)
      Some((x1e, os.head, ds, os, ato, false))
    } else if (sharedSfxe.nonEmpty) {
      val x1e = sharedSfxe.head
      val (ds, os, ato) =
        if (doubledSuffix(lhse).contains(x1e)) (lhse, rhse, l2e)
        else                                    (rhse, lhse, l1e)
      Some((x1e, os.last, ds, os, ato, true))
    } else None
  }

  /**
   * Normalize equations where x1/x2 are already in the same commutation class
   * (AddAxiom + RemoveFacts, no branching).  Also normalizes all matched equations
   * beyond the first one.  Called after nielsenCommutationSplit returns List().
   */
  def nielsenNormalize: Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val o = order

    // computeCommutationClasses already folds in the binary commutativity
    // encoding (a.b = t and b.a = t  =>  {a,b}), so we use it as the single
    // source of commutation classes here.
    val rawClasses = computeCommutationClasses()
    if (rawClasses.isEmpty) return List()
    val composites: Set[LinearCombination] = (for {
      (res, lits) <- concatPerRes
      lit         <- lits
      a = lit(0); b = lit(1)
      if isUngrounded(a) && isUngrounded(b)
    } yield res).toSet
    val knownClasses = rawClasses.map(cls => cls.filter(z => !composites.contains(z)))
                                 .filter(_.size >= 2)
    if (knownClasses.isEmpty) return List()
    Console.err.println("[Nielsen-norm] comm classes (leaf only): " +
      knownClasses.map(cls => "{" + cls.map(term2String).mkString(", ") + "}").mkString(", "))
    val elemToClass = (for (cls <- knownClasses; z <- cls) yield z -> cls).toMap

    // Class shared by the FIRST element of both sides (prefix zone), if any.
    def prefixClass(d   : Seq[LinearCombination],
                    oth : Seq[LinearCombination])
        : Option[Set[LinearCombination]] =
      d.headOption.flatMap(h => if (isUngrounded(h)) elemToClass.get(h) else None)
       .filter(cls => oth.headOption.exists(h => isUngrounded(h) && cls.contains(h)))

    // Class shared by the LAST element of both sides (suffix zone), if any.
    def suffixClass(d   : Seq[LinearCombination],
                    oth : Seq[LinearCombination])
        : Option[Set[LinearCombination]] =
      d.lastOption.flatMap(h => if (isUngrounded(h)) elemToClass.get(h) else None)
       .filter(cls => oth.lastOption.exists(h => isUngrounded(h) && cls.contains(h)))

    val normActions = new ArrayBuffer[Plugin.Action]

    for ((res, lits) <- concatPerRes if lits.size >= 2) {
      for (i <- lits.indices; j <- (i + 1) until lits.size) {
        val l1e  = lits(i); val l2e = lits(j)
        val lhse = flattenTerm(l1e(0)) ++ flattenTerm(l1e(1))
        val rhse = flattenTerm(l2e(0)) ++ flattenTerm(l2e(1))

        // An equation of the form a.b == b.a is the very fact that *defines*
        // the commutation class {a,b}.  Normalizing it would collapse it to a
        // trivial equation and destroy the class, so it must be left untouched.
        if (isCommProxy(Seq(l1e, l2e))) {
          Console.err.println("[Nielsen-comm-norm] skip (defines commutativity): " +
            lhse.map(term2String).mkString(".") + " == " +
            rhse.map(term2String).mkString("."))
        } else {

        // First, attempt both-end cancellation: prefer simultaneous
        // prefix+suffix normalization (cancel P1 and P2) when it applies.
        var normalizedByBothEnds = false
        for (cls <- knownClasses if !normalizedByBothEnds) {
          val (p1, p2, remD, remO) = cancelBothEnds(lhse, rhse, cls)
          val cancelled = p1.nonEmpty || p2.nonEmpty
          if (cancelled && remD.nonEmpty && remO.nonEmpty) {
            val normFormula = {
              val builder = new FormulaBuilder(goal, theory)
              val resMid = builder.newVar(StringSort)
              val pChain : Seq[Term] =
                p1.map(z => z : Term) ++ Seq(resMid : Term) ++ p2.map(z => z : Term)
              builder.addConcatN(pChain, res)   // res = P1 · res' · P2
              builder.addConcatN(remD, resMid)  // remD == res'
              builder.addConcatN(remO, resMid)  // remO == res'
              builder.result
            }

            DecisionTreeLogger.addNode(Seq(
              "rule"             -> DecisionTreeLogger.str("nielsenNormalizeBothEnds"),
              "kind"             -> DecisionTreeLogger.str(
                                      "commutation-class normalization + cancel (both ends)"),
              "commutationClass" -> DecisionTreeLogger.strArr(cls.toSeq.map(term2String)),
              "before"           -> DecisionTreeLogger.str(lhse.map(term2String).mkString(".") + " == " + rhse.map(term2String).mkString(".")),
              "after"            -> DecisionTreeLogger.str(remD.map(term2String).mkString(".") + " == " + remO.map(term2String).mkString("."))
            ))

            normActions += Plugin.AddAxiom(concatLits ++ lengthLits, normFormula, theory)
            normActions += Plugin.RemoveFacts(Conjunction.conj(List(l1e, l2e), order))
            normalizedByBothEnds = true
          }
        }

        if (!normalizedByBothEnds) {
          // Normalize the prefix commutation zone first, then the suffix zone of
          // the (possibly already prefix-normalized) sequences.  Suffix
          // normalization only reorders the trailing leaf zone and keeps the
          // head, so chaining the two is safe and terminating.
          var normD = lhse
          var normO = rhse
          for (cls <- prefixClass(normD, normO)) {
            val (nd, no) = normalizedSeqBoth(normD, normO, cls, isSuffix = false)
            normD = nd; normO = no
          }
          for (cls <- suffixClass(normD, normO)) {
            val (nd, no) = normalizedSeqBoth(normD, normO, cls, isSuffix = true)
            normD = nd; normO = no
          }

          if (normD != lhse || normO != rhse) {
            val normFormula = {
              val builder = new FormulaBuilder(goal, theory)
              if (normD.nonEmpty) builder.addConcatN(normD, res)
              if (normO.nonEmpty) builder.addConcatN(normO, res)
              builder.result
            }
            Console.err.println("[Nielsen-comm-norm] normalizing on result " +
              term2String(res))
            Console.err.println("  before: " + lhse.map(term2String).mkString(".") +
              " == " + rhse.map(term2String).mkString("."))
            Console.err.println("  after:  " + normD.map(term2String).mkString(".") +
              " == " + normO.map(term2String).mkString("."))
            normActions += Plugin.AddAxiom(concatLits ++ lengthLits, normFormula, theory)
            normActions += Plugin.RemoveFacts(Conjunction.conj(List(l1e, l2e), order))
          } else {
            Console.err.println("[Nielsen-comm-norm] already normal: " +
              lhse.map(term2String).mkString(".") + " == " + rhse.map(term2String).mkString("."))
          }
        }
        } // end else (not a commutativity-defining equation)
      }
    }

    normActions.toSeq
  }


  /**
   * Nielsen commutation split: for the FIRST matched equation produce a 3-way
   * AxiomSplit (comm + k=J + k=J-1).  The comm branch encodes x1*x2=x2*x1 and
   * adds the length bound len(x1) <= (J-1)*len(x2).
   *
   * If the length bound is already present in the arithmetic facts (Diophantine
   * constraints), the split is skipped so that nielsenNormalize can run instead.
   */
  def nielsenCommutationSplit: Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val o = order

    val eqs = findEquationsWithPrefixSuffixShared()
    if (eqs.isEmpty) return List()

    // Skip equations whose two split variables are ALREADY in the same
    // commutation class.  The comm branch only registers x1*x2 = x2*x1; once
    // that fact holds, re-splitting the same equation makes no progress and the
    // splitter loops forever, re-deriving the identical 3-way split.  Such
    // equations are left to nielsenNormalize / the standard Nielsen step.
    val knownClasses = computeCommutationClasses()
    def alreadyCommute(a : LinearCombination, b : LinearCombination) : Boolean =
      knownClasses.exists(c => c.contains(a) && c.contains(b))
    def runLen(os : Seq[LinearCombination], x2 : LinearCombination,
               isSfx : Boolean) : Int =
      if (isSfx) os.reverseIterator.takeWhile(_ == x2).length
      else       os.iterator.takeWhile(_ == x2).length
    val splittable = eqs.filter {
      case (l1e, l2e, _, lhse, rhse, sp, ss) =>
        extractCommPattern(l1e, l2e, lhse, rhse, sp, ss) match {
          case Some((px1, px2, _, pos, _, pSfx)) =>
            // Genuine thesis §3.3 regime only (J >= 2).  At J <= 1 the comm
            // range 1<=k<=J-2 is empty and the comm branch degenerates, so the
            // split cannot make progress and loops — leave such equations to
            // the standard Nielsen splitter.
            !alreadyCommute(px1, px2) && runLen(pos, px2, pSfx) >= 2
          case None => false
        }
    }
    // Entry diagnostics: print on EVERY call (even when we bail out), so we can
    // see whether the pristine x^J…==y^J… equation is visible here at all, or
    // whether it was already decomposed before comm-split got a chance to run.
    Console.err.println("[Nielsen-comm-entry] eqs.size=" + eqs.size +
      "  splittable.size=" + splittable.size)
    for ((l1e, l2e, _, lhse, rhse, sp, ss) <- eqs) {
      val patStr = extractCommPattern(l1e, l2e, lhse, rhse, sp, ss) match {
        case Some((a, b, _, pos, _, sfx)) =>
          "x1=" + term2String(a) + " x2=" + term2String(b) +
          " run=" + runLen(pos, b, sfx) + " alreadyCommute=" + alreadyCommute(a, b) +
          " isSuffix=" + sfx
        case None => "no-pattern"
      }
      Console.err.println("[Nielsen-comm-entry]   eq: " +
        lhse.map(term2String).mkString(".") + " == " +
        rhse.map(term2String).mkString(".") + "   [" + patStr + "]")
    }

    if (splittable.isEmpty) return List()

    Console.err.println("[Nielsen-comm-split] current equations:")
    Console.err.println("[Nielsen-comm-split] eqs.size=" + eqs.size)
    printFlatEquations("[Nielsen-comm-split]")

    val (l1, l2, res, lhs, rhs, sharedPfx, sharedSfx) = splittable.head
    val actions = new ArrayBuffer[Plugin.Action]

    def doSplit(x1          : LinearCombination,
                x2          : LinearCombination,
                doubledSide : Seq[LinearCombination],
                otherSide   : Seq[LinearCombination],
                atomToRemove: Atom,
                isSuffix    : Boolean): Unit = {

      val J  = if (isSuffix) otherSide.reverseIterator.takeWhile(_ == x2).length
               else          otherSide.iterator.takeWhile(_ == x2).length
      val J1 = math.max(1, J - 1)

      val x1s = term2String(x1); val x2s = term2String(x2)
      val crossLabel = if (x1 == x2 || lhs.contains(x2) || rhs.contains(x1)) "same" else "cross"
      Console.err.println("[Nielsen-comm-split] " + crossLabel +
        (if (isSuffix) "-suffix" else "-prefix") +
        "  x1=" + x1s + "  x2=" + x2s + "  J=" + J + "  J1=" + J1)

      // Branch 1 (comm): примитивный корень p,q  с  x2=p.q, x1=x2^(J-2).p,
      //   u=p.q=q.p  =>  {p,q} класс коммутации; t=x1.x2=x2.x1  =>  {x1,x2} тоже.
      // commRestated becomes true once the equation is fully re-expressed over
      // p,q in normalized form below; only then may the comm branch drop the
      // original atoms (otherwise the equation would be lost).
      var commRestated = false
      val commFormula = {
        val builder = new FormulaBuilder(goal, theory)
        val p = builder.newVar(StringSort)
        val q = builder.newVar(StringSort)
        val u = builder.newVar(StringSort)
        builder.addConcat(p, q, x2)
        builder.addConcat(p, q, u)
        builder.addConcat(q, p, u)
        Console.err.println("builder: " + builder)
        val k = math.max(0, J - 2)
        if (isSuffix) builder.addConcatN(p +: Seq.fill(k)(x2 : Term), x1)
        else          builder.addConcatN(Seq.fill(k)(x2 : Term) :+ p, x1)
        val t = builder.newVar(StringSort)
        builder.addConjunct(_str_++(List(l(x1), l(x2), l(t))))
        builder.addConjunct(_str_++(List(l(x2), l(x1), l(t))))

        // Insertion via p,q: rewrite the equation over the freshly introduced
        // primitive-root pieces (x2 = p.q, x1 = x2^(J-2).p) and normalize for the
        // commutation class {p,q} — p.q = q.p was just asserted, so p and q
        // commute.  Cancel the common p/q block at BOTH ends.  When this fires,
        // res = P1·resMid·P2 with remD == remO == resMid fully restates the
        // equation over p,q, so the original atoms become redundant (commRestated)
        // and the comm branch removes them just like the boundary branches.
        {
          val pLC : LinearCombination = l(p)
          val qLC : LinearCombination = l(q)
          val pqClass = Set(pLC, qLC)
          // x1 = x2^k . p  (prefix) / p . x2^k  (suffix), with x2 = p.q, k=J-2.
          val x1Exp : Seq[LinearCombination] =
            if (isSuffix) pLC +: Seq.fill(k)(Seq(pLC, qLC)).flatten
            else          Seq.fill(k)(Seq(pLC, qLC)).flatten :+ pLC
          def expandPQ(side : Seq[LinearCombination]) : Seq[LinearCombination] =
            side.flatMap { z =>
              if      (z == x2) Seq(pLC, qLC)
              else if (z == x1) x1Exp
              else              Seq(z)
            }
          val dsExp = expandPQ(doubledSide)
          val osExp = expandPQ(otherSide)
          Console.err.println("[Nielsen-comm-split] p.q-insert  dsExp=" +
            dsExp.map(term2String).mkString(".") + "  osExp=" +
            osExp.map(term2String).mkString("."))
          val (p1, p2, remD, remO) = cancelBothEnds(dsExp, osExp, pqClass)
          val cancelled = p1.nonEmpty || p2.nonEmpty
          Console.err.println("[Nielsen-comm-split] cancelBothEnds" +
            "  P1=" + p1.map(term2String).mkString(".") +
            "  P2=" + p2.map(term2String).mkString(".") +
            "  remD=" + remD.map(term2String).mkString(".") +
            "  remO=" + remO.map(term2String).mkString(".") +
            "  cancelled=" + cancelled)
          if (cancelled && remD.nonEmpty && remO.nonEmpty) {
            val resMid = builder.newVar(StringSort)
            val pChain : Seq[Term] =
              p1.map(z => z : Term) ++ Seq(resMid : Term) ++ p2.map(z => z : Term)
            builder.addConcatN(pChain, res)
            builder.addConcatN(remD.map(z => z : Term), resMid)
            builder.addConcatN(remO.map(z => z : Term), resMid)
            commRestated = true
            Console.err.println("[Nielsen-comm-split] RESTATE (commRestated=true): " +
              "res = " + pChain.map(term2String).mkString(".") +
              " ;  resMid = " + remD.map(term2String).mkString(".") +
              " == " + remO.map(term2String).mkString(".") +
              "  -> remove original atoms")
          }
        }

        if (J1 > 0) {
          for (lenX1 <- lengthMap.get(x1); lenX2 <- lengthMap.get(x2))
            builder.addConjunct(
              sum(List((IdealInt(J1), l(lenX2)), (IdealInt.MINUS_ONE, l(lenX1)))) >= 0
            )
        }

        builder.result
      }

      // Build the boundary-case formula  x1 = x2^k . q  (k = J or J-1) together
      // with the SUBSTITUTED restatement of this equation referencing res, so
      // the original atoms can be removed (breaking the re-split loop) without
      // losing the equation.  After substitution the doubled side starts with
      // x2^k just like the other side, and the leading x2-run cancels via the
      // standard prefix rule — exactly eqs. (8)/(9) of the thesis §3.3.
      def boundaryFormula(k : Int, withLenBound : Boolean) = {
        val builder = new FormulaBuilder(goal, theory)
        val q = builder.newVar(StringSort)
        val repl : Seq[Term] =
          if (isSuffix) (q : Term) +: Seq.fill(k)(x2 : Term)
          else          Seq.fill(k)(x2 : Term) :+ (q : Term)
        builder.addConcatN(repl, x1)            // x1 = x2^k . q  (propagates to all eqs)
        // Short-remainder bound |q| < |x2|: kept ONLY for the k=J-1 branch; the
        // k=J branch leaves q unbounded.
        if (withLenBound)
          for (lenX2 <- lengthMap.get(x2)) {
            val lenQ = builder.lengthOfTerm(q)
            builder.addConjunct(l(lenX2) - l(lenQ) >= 1)
          }
        // Restate THIS equation with x1 substituted out of the doubled side.
        val dsSub : Seq[Term] =
          doubledSide.flatMap(z => if (z == x1) repl else Seq(z : Term))
        if (dsSub.nonEmpty)        builder.addConcatN(dsSub, res)
        if (otherSide.nonEmpty)    builder.addConcatN(otherSide.map(z => z : Term), res)
        // (1) the equation that gets INSERTED:  x1 = x2^k . q  (+ bound for k=J-1)
        Console.err.println("[Nielsen-comm-split] boundaryFormula(k=" + k +
          ") вставляется:  " +
          term2String(x1) + " = " + repl.map(term2String).mkString(".") +
          (if (withLenBound) "  ,  |q| < |" + term2String(x2) + "|" else ""))
        // (2) the equation AFTER insertion (x1 substituted out of the doubled side):
        Console.err.println("[Nielsen-comm-split] boundaryFormula(k=" + k +
          ") после вставки:  " +
          dsSub.map(term2String).mkString(".") + " == " +
          otherSide.map(term2String).mkString(".") + "  (= res)")
        builder.result
      }

      // Branch 2 (k=J): x1 = x2^J . q,  |q| < |x2| (short remainder).
      // The bound is REQUIRED for soundness: it keeps k=J a bounded base case
      // (len(x1) < (J+1)*len(x2)).  Dropping it yielded spurious models that
      // violate the other constraints (suffixof / lengths).
      val caseJFormula  = boundaryFormula(J,  withLenBound = true)

      // Branch 3 (k=J-1): x1 = x2^(J-1) . q,  |q| < |x2| (short remainder)
      val caseJ1Formula = boundaryFormula(J1, withLenBound = true)

      val lenBound =      // |q|<|x2| applies to both boundary branches
        if (lengthMap.contains(x2)) "  |q|<|" + x2s + "|" else ""
      val k2 = math.max(0, J - 2)
      val pqExp = "(" + x2s + ")"
      val x1Exp = if (k2 == 0) "p"
                  else if (isSuffix) "p." + Seq.fill(k2)(pqExp).mkString(".")
                  else Seq.fill(k2)(pqExp).mkString(".") + ".p"
      val branch1Str = "comm: " + x2s + "=p.q, p.q=q.p  " + x1s + "=" + x1Exp +
        (if (J1 > 0) "  len(" + x1s + ")<="+J1+"*len("+x2s+")" else "")
      val branch2Str = "k=J: " + x1s + "="+Seq.fill(J)(x2s).mkString(".")+ ".q" + lenBound
      val branch3Str = "k=J-1: " + x1s + "="+Seq.fill(J1)(x2s).mkString(".")+".q" + lenBound
      Console.err.println("  Branch 1 (" + branch1Str + ")")
      Console.err.println("  Branch 2 (" + branch2Str + ")")
      Console.err.println("  Branch 3 (" + branch3Str + ")")

      DecisionTreeLogger.addNode(Seq(
        "rule"     -> DecisionTreeLogger.str("nielsenCommutationSplit"),
        "kind"     -> DecisionTreeLogger.str(
                        crossLabel + (if (isSuffix) "-suffix" else "-prefix")),
        "x1"       -> DecisionTreeLogger.str(x1s),
        "x2"       -> DecisionTreeLogger.str(x2s),
        "J"        -> DecisionTreeLogger.num(J),
        "J1"       -> DecisionTreeLogger.num(J1),
        "action"   -> DecisionTreeLogger.str(
                        "Plugin.AxiomSplit (" + (if (J != J1) 3 else 2) + "-way)"),
        "equation" -> DecisionTreeLogger.str(
                        lhs.map(term2String).mkString(".") + " == " +
                        rhs.map(term2String).mkString(".")),
        "branches" -> DecisionTreeLogger.strArr(
                        if (J != J1) Seq(branch1Str, branch2Str, branch3Str)
                        else         Seq(branch1Str, branch2Str))
      ))

      val doubledAtom : Atom = if (atomToRemove eq l2) l1 else l2
      // The boundary branches restate this equation in substituted form, so the
      // two original atoms must be removed; otherwise the unchanged equation is
      // re-matched and the split fires again forever.  The comm branch now also
      // restates it — over p,q in normalized form — whenever commRestated holds,
      // so in that case it removes the original atoms too.  If nothing cancelled
      // (commRestated == false) the equation is only augmented with x1*x2=x2*x1
      // and must be KEPT, relying on the already-commute gate to stop re-splitting.
      val removeBoth = List(Plugin.RemoveFacts(
                              Conjunction.conj(List(atomToRemove, doubledAtom), order)))
      val commActions : List[Plugin.Action] =
        if (commRestated) removeBoth else List[Plugin.Action]()

      // State the split is applied to (for diagnosing spurious models).
      dumpState("[Nielsen-comm-split][state]")

      // When J == J1 (e.g. J=1 → J1=1), Branch 2 and Branch 3 are identical — use 2-way split.
      // NB: an AxiomSplit MUST be exhaustive — its branch disjunction is assumed
      // by Princess as a fact.  Dropping any branch (e.g. commenting out k=J)
      // makes comm ∨ k=J-1 NON-exhaustive, so Princess accepts spurious models
      // (observed: x1="AAAA", x2="AA" violating suffixof / lengths).  All three
      // boundary/comm cases are required.
      // DIAGNOSTIC branch selector: COMM_BRANCH_SEL = comm | kJ | kJ1 | all
      // (default all).  Isolates which flip branch admits a spurious model by
      // running the split with only that branch live.
      val sel = Option(System.getenv("COMM_BRANCH_SEL")).getOrElse("all")
      // DIAGNOSTIC: if COMM_KEEP_EQ is set, boundary branches do NOT removeBoth
      // (keep the original equation so it stays string-splittable).
      val boundaryActions : List[Plugin.Action] =
        if (Option(System.getenv("COMM_KEEP_EQ")).isDefined) List() else removeBoth
      val labelled =
        List(("comm", commFormula, commActions),
             ("kJ",   caseJFormula, boundaryActions),
             ("kJ1",  caseJ1Formula, boundaryActions))
      val live =
        if (J == J1) labelled.filter(_._1 != "comm") else labelled
      val chosen = sel match {
        case "comm" => live.filter(_._1 == "comm")
        case "kJ"   => live.filter(_._1 == "kJ")
        case "kJ1"  => live.filter(_._1 == "kJ1")
        case _      => live
      }
      Console.err.println("[Nielsen-comm-split] BRANCH_SEL=" + sel +
        "  live branches: " + chosen.map(_._1).mkString(","))
      val splitBranches = chosen.map(t => (t._2, t._3))

      actions += Plugin.AxiomSplit(concatLits ++ lengthLits, splitBranches, theory)
    }

    // Orientation by known length: x1 = x2^k·q is only valid when |x1| >= |x2|.
    // If the goal already entails that the base x2 is STRICTLY longer than the
    // doubled variable x1, flip the roles and decompose x2 = x1^k·q instead
    // (|q| < |x1|).  Swapping the doSplit arguments makes BOTH the boundary
    // branches AND the comm branch symmetric w.r.t. the equals sign, since they
    // are all parameterized through (x1, x2, doubledSide, otherSide).
    // Provable lower bound on len(a) - len(b) via reduceWithFacts, or None if
    // either length is unknown.
    def lenLB(a : LinearCombination, b : LinearCombination) : Option[IdealInt] =
      (lengthMap.get(a), lengthMap.get(b)) match {
        case (Some(la), Some(lb)) => goal.reduceWithFacts.lowerBound(l(la) - l(lb))
        case _                    => None
      }
    // len(a) > len(b) is PROVABLY entailed (lower bound on the difference >= 1).
    def knownLonger(a : LinearCombination, b : LinearCombination) : Boolean =
      lenLB(a, b) match { case Some(v) => v.signum > 0; case None => false }

    // FLIP is currently UNSOUND: when it fires (goal locally entails
    // len(x1)>len(x2)), the swapped k=J branch restates the equation and
    // removeBoth-drops the original; the restatement is then ABSTRACTED into
    // Parikh/char-count constraints before being string-split, so a model with
    // matching char-counts but wrong character ORDER is enumerated (bogus sat).
    // The string equation is already gone by the Final state, so forcing a split
    // there cannot help.  A proper fix is at the reducer/decomposition level
    // (keep the restated equation string-split before Parikh abstraction) and is
    // high-risk; left disabled.  Default orientation (decompose the doubled
    // variable) is sound.
    val FLIP_FIX = false

    for ((x1, x2, ds, os, ato, isSfx) <-
         extractCommPattern(l1, l2, lhs, rhs, sharedPfx, sharedSfx)) {
      // Guard: if the goal PROVABLY entails BOTH len(x1)>len(x2) AND
      // len(x2)>len(x1), its length facts are contradictory — the goal is
      // already unsat.  Splitting here would removeBoth the equation whose
      // length implications witness that contradiction, unsoundly rescuing the
      // unsat goal into a spurious model.  Skip the comm-split; the standard
      // Nielsen splitter / arithmetic will close the goal.
      if (knownLonger(x1, x2) && knownLonger(x2, x1)) {
        Console.err.println("[Nielsen-comm-split] SKIP: contradictory lengths " +
          "len(" + term2String(x1) + ")-len(" + term2String(x2) + ")=" +
          lenLB(x1, x2) + ", reverse=" + lenLB(x2, x1) + " (goal already unsat)")
      } else if (FLIP_FIX && knownLonger(x2, x1)) {
        Console.err.println("[Nielsen-comm-split] FLIP orientation: |" +
          term2String(x2) + "| > |" + term2String(x1) + "|  -> decompose " +
          term2String(x2) + " = " + term2String(x1) + "^k.q")
        doSplit(x2, x1, os, ds, (if (ato eq l1) l2 else l1), isSfx)
      } else
        doSplit(x1, x2, ds, os, ato, isSfx)
    }

    actions.toSeq
  }

  def printSharedNonTerminalEquations() : Unit = {
    val classes = computeCommutationClasses()
    Console.err.println("=== Commutation classes (" + classes.size + ") ===")
    for ((cls, i) <- classes.zipWithIndex)
      Console.err.println("  [" + i + "] " + cls.map(term2String).mkString(", "))
    Console.err.println("===========================================")

    if (classes.isEmpty) return

    // Map each non-terminal to its commutation class
    val elemToClass: Map[LinearCombination, Set[LinearCombination]] =
      (for (cls <- classes; z <- cls) yield z -> cls).toMap

    val eqs = findEquationsWithPrefixSuffixShared()
    Console.err.println("=== Equations with pattern a.a...==b.a... (" + eqs.size + ") ===")
    for ((_, _, _, lhs, rhs, sharedPfx, sharedSfx) <- eqs) {
      Console.err.println("  " + lhs.map(term2String).mkString(" . ") +
                          " == " + rhs.map(term2String).mkString(" . "))

      val pfxClasses = sharedPfx.toSeq.flatMap(elemToClass.get).distinct
      val sfxClasses = sharedSfx.toSeq.flatMap(elemToClass.get).distinct
      for (cls <- pfxClasses)
        normalizeWithCommutationClass(lhs, rhs, cls, isSuffix = false)
      for (cls <- sfxClasses)
        normalizeWithCommutationClass(lhs, rhs, cls, isSuffix = true)
    }
    Console.err.println("==================================================================================")
  }

  private def printCurrentRules() : Unit = {
    Console.err.println("=== OstrichNielsenSplitter: word equations at this stage ===")
    var count = 0
    for ((res, lits) <- concatPerRes; if lits.size >= 2) {
      for (i <- lits.indices; j <- (i + 1) until lits.size) {
        val l1 = lits(i)
        val l2 = lits(j)
        val lhs = expandedSideStr(l1(0)) + " . " + expandedSideStr(l1(1))
        val rhs = expandedSideStr(l2(0)) + " . " + expandedSideStr(l2(1))
        Console.err.println("  " + lhs + " == " + rhs)
        count += 1
      }
    }
    if (count == 0) Console.err.println("  (none)")
    Console.err.println("Length literals (" + lengthLits.size + "):")
    for (lit <- lengthLits)
      Console.err.println("  |" + term2String(lit(0)) + "| == " + lit(1))
    Console.err.println("============================================================")
    printSharedNonTerminalEquations()
  }

}
