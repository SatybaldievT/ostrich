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
  val predConj     = facts.predConj
  val concatLits   = predConj.positiveLitsWithPred(_str_++)
  val concatPerRes = concatLits groupBy (_(2))
  val lengthLits   = predConj.positiveLitsWithPred(_str_len)
  val lengthMap    = (for (a <- lengthLits.iterator) yield (a(0), a(1))).toMap

  def resolveConcat(t : LinearCombination)
                  : Option[(LinearCombination, LinearCombination)] =
    for (lits <- concatPerRes get t) yield (lits.head(0), lits.head(1))

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
  def splitEquation : Seq[Plugin.Action] = {
    val multiGroups =
      concatPerRes filter {
        case (res, lits) => lits.size >= 2 && !(strDatabase isConcrete res)
      }

    val splittableTerms =
      concatLits.iterator.map(_(2)).filter(multiGroups.keySet).toList.distinct

    if (splittableTerms.isEmpty)
      return List()

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
      splitEquationWithLen(splitLit1, splitLit2, multiGroups.size)
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

  // Returns non-terminals that appear at least twice in the first 2 positions
  private def doubledPrefix(seq: Seq[LinearCombination]): Set[LinearCombination] = {
    val pfx = seq.take(2)
    pfx.filter(t => isNonTerminal(t) && pfx.count(_ == t) >= 2).toSet
  }

  // Returns non-terminals that appear at least twice in the last 2 positions
  private def doubledSuffix(seq: Seq[LinearCombination]): Set[LinearCombination] = {
    val sfx = seq.takeRight(2)
    sfx.filter(t => isNonTerminal(t) && sfx.count(_ == t) >= 2).toSet
  }

  private def prefixNonTerms(seq: Seq[LinearCombination]): Set[LinearCombination] =
    seq.take(2).filter(isNonTerminal).toSet

  private def suffixNonTerms(seq: Seq[LinearCombination]): Set[LinearCombination] =
    seq.takeRight(2).filter(isNonTerminal).toSet

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

        val lhsFirstIsNT = lhs.nonEmpty && isNonTerminal(lhs.head)
        val rhsFirstIsNT = rhs.nonEmpty && isNonTerminal(rhs.head)
        val lhsLastIsNT  = lhs.nonEmpty && isNonTerminal(lhs.last)
        val rhsLastIsNT  = rhs.nonEmpty && isNonTerminal(rhs.last)

        // a.a... == b.a... : doubled in one prefix, other side also starts with non-terminal
        val sharedPrefix =
          (if (rhsFirstIsNT) doubledPrefix(lhs) intersect prefixNonTerms(rhs)
           else Set.empty[LinearCombination]) ++
          (if (lhsFirstIsNT) doubledPrefix(rhs) intersect prefixNonTerms(lhs)
           else Set.empty[LinearCombination])

        // ...a.a == ...a.b : doubled in one suffix, other side also ends with non-terminal
        val sharedSuffix =
          (if (rhsLastIsNT) doubledSuffix(lhs) intersect suffixNonTerms(rhs)
           else Set.empty[LinearCombination]) ++
          (if (lhsLastIsNT) doubledSuffix(rhs) intersect suffixNonTerms(lhs)
           else Set.empty[LinearCombination])

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

  def computeCommutationClasses()
      : Seq[Set[LinearCombination]] = {
    val parent = new MHashMap[LinearCombination, LinearCombination]()

    for ((res, lits) <- concatPerRes; if lits.size >= 2) {
      for (i <- lits.indices; j <- (i + 1) until lits.size) {
        val l1  = lits(i)
        val l2  = lits(j)
        val lhs = expandTerm(l1(0)) ++ expandTerm(l1(1))
        val rhs = expandTerm(l2(0)) ++ expandTerm(l2(1))

        val lhsFirstIsNT = lhs.nonEmpty && isNonTerminal(lhs.head)
        val rhsFirstIsNT = rhs.nonEmpty && isNonTerminal(rhs.head)
        val lhsLastIsNT  = lhs.nonEmpty && isNonTerminal(lhs.last)
        val rhsLastIsNT  = rhs.nonEmpty && isNonTerminal(rhs.last)

        // prefix: a.a... == b.a...  =>  a commutes with b
        if (rhsFirstIsNT)
          for (a <- doubledPrefix(lhs); if prefixNonTerms(rhs).contains(a))
            ufUnion(parent, a, rhs.head)
        if (lhsFirstIsNT)
          for (a <- doubledPrefix(rhs); if prefixNonTerms(lhs).contains(a))
            ufUnion(parent, a, lhs.head)

        // suffix: ...a.a == ...b.a  =>  a commutes with b
        if (rhsLastIsNT)
          for (a <- doubledSuffix(lhs); if suffixNonTerms(rhs).contains(a))
            ufUnion(parent, a, rhs.last)
        if (lhsLastIsNT)
          for (a <- doubledSuffix(rhs); if suffixNonTerms(lhs).contains(a))
            ufUnion(parent, a, lhs.last)
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
    (normDoubled, normOther)
  }

  /**
   * Nielsen split for the commutativity pattern a.a...==b.a... / ...a.a==...a.b.
   *
   * For the FIRST matched equation: AxiomSplit into two branches
   *   Branch 1 — comm:  assert x1.x2 = x2.x1, replace BOTH atoms with
   *                     their normalized forms (P.RL.U' and P.RR.V').
   *   Branch 2 — split: introduce fresh q,
   *                     prefix: assert x2 = x1.q, add x1.rest1 = q.x1.rest2
   *                     suffix: assert x2 = q.x1, add rest1.x1 = rest2.x1.q
   *
   * For ALL OTHER matched equations: direct normalization (AddAxiom + RemoveFacts,
   * no branching), applied before the split on the first equation.
   */
  def nielsenCommutationSplit: Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val o = order

    val eqs = findEquationsWithPrefixSuffixShared()
    if (eqs.isEmpty) return List()

    val actions = new ArrayBuffer[Plugin.Action]

    // Helper: extract the (x1, doubledSide, otherSide, atomToRemove, isSuffix) pattern
    // from one equation tuple.  Returns None if neither prefix nor suffix pattern applies.
    def extractPattern(l1e : Atom, l2e : Atom,
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
        val x2e = os.head
        Some((x1e, x2e, ds, os, ato, false))
      } else if (sharedSfxe.nonEmpty) {
        val x1e = sharedSfxe.head
        val (ds, os, ato) =
          if (doubledSuffix(lhse).contains(x1e)) (lhse, rhse, l2e)
          else                                    (rhse, lhse, l1e)
        val x2e = os.last
        Some((x1e, x2e, ds, os, ato, true))
      } else None
    }

    // For equations beyond the first: normalize directly (no branching).
    for ((l1e, l2e, rese, lhse, rhse, sharedPfxe, sharedSfxe) <- eqs.tail) {
      for ((x1e, x2e, dse, ose, ato, isSfx) <-
           extractPattern(l1e, l2e, lhse, rhse, sharedPfxe, sharedSfxe)) {
        val clse = Set(x1e, x2e)
        val (normD, normO) = normalizedSeqBoth(dse, ose, clse, isSfx)
        val normFormula = {
          val builder = new FormulaBuilder(goal, theory)
          if (normD.nonEmpty) builder.addConcatN(normD, rese)
          if (normO.nonEmpty) builder.addConcatN(normO, rese)
          builder.result
        }
        val doubledAtome: Atom = if (ato eq l2e) l1e else l2e
        Console.err.println("[Nielsen-norm] direct: " +
          lhse.map(term2String).mkString(".") + " == " + rhse.map(term2String).mkString("."))
        Console.err.println("  norm: " + normD.map(term2String).mkString(" . ") +
                            " == " + normO.map(term2String).mkString(" . "))
        actions += Plugin.AddAxiom(concatLits ++ lengthLits, normFormula, theory)
        actions += Plugin.RemoveFacts(Conjunction.conj(List(ato, doubledAtome), order))
      }
    }

    // For the first equation: full AxiomSplit (comm branch vs split branch).
    val (l1, l2, res, lhs, rhs, sharedPfx, sharedSfx) = eqs.head

    def doSplit(x1          : LinearCombination,
                x2          : LinearCombination,
                doubledSide : Seq[LinearCombination],
                otherSide   : Seq[LinearCombination],
                atomToRemove: Atom,
                isSuffix    : Boolean): Unit = {

      val cls = Set(x1, x2)
      val (normDoubled, normOther) =
        normalizedSeqBoth(doubledSide, otherSide, cls, isSuffix)

      // Branch 1: commutativity — x1.x2 = x2.x1.
      // Replace BOTH original atoms with their normalized forms.
      val commFormula = {
        val builder = new FormulaBuilder(goal, theory)
        val t = builder.newVar(StringSort)
        builder.addConcat(x1, x2, t)
        builder.addConcat(x2, x1, t)
        if (normDoubled.nonEmpty) builder.addConcatN(normDoubled, res)
        if (normOther.nonEmpty)   builder.addConcatN(normOther,   res)
        builder.result
      }

      // Branch 2: split — introduce q.
      // prefix: x2 = x1.q, new eq: x1.rest1 = q.x1.rest2
      // suffix: x2 = q.x1, new eq: rest1.x1 = rest2.x1.q
      val splitFormula = {
        val builder = new FormulaBuilder(goal, theory)
        val q    = builder.newVar(StringSort)
        val rNew = builder.newVar(StringSort)
        if (isSuffix) {
          builder.addConcat(q, x1, x2)
          builder.addConcatN(doubledSide.dropRight(1), rNew)
          builder.addConcatN(otherSide.dropRight(1) :+ q, rNew)
        } else {
          builder.addConcat(x1, q, x2)
          builder.addConcatN(doubledSide.drop(1), rNew)
          builder.addConcatN(q +: otherSide.drop(1), rNew)
        }
        builder.result
      }

      val patLabel = if (isSuffix) "suffix" else "prefix"
      Console.err.println("[Nielsen-comm-split] " + patLabel + ": " +
        lhs.map(term2String).mkString(".") + " == " + rhs.map(term2String).mkString("."))
      Console.err.println("  x1=" + term2String(x1) + "  x2=" + term2String(x2))
      Console.err.println("  norm-doubled: " + normDoubled.map(term2String).mkString(" . "))
      Console.err.println("  norm-other:   " + normOther.map(term2String).mkString(" . "))

      val doubledAtom: Atom = if (atomToRemove eq l2) l1 else l2
      val removeBoth  = Conjunction.conj(List(atomToRemove, doubledAtom), order)
      val removeOther = Conjunction.conj(atomToRemove, order)

      actions += Plugin.AxiomSplit(
        concatLits ++ lengthLits,
        List(
          (commFormula,  List(Plugin.RemoveFacts(removeBoth))),
          (splitFormula, List(Plugin.RemoveFacts(removeOther)))
        ),
        theory
      )
    }

    for ((x1, x2, ds, os, ato, isSfx) <-
         extractPattern(l1, l2, lhs, rhs, sharedPfx, sharedSfx))
      doSplit(x1, x2, ds, os, ato, isSfx)

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
