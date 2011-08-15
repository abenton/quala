package quala.util.parsing.combinator

import quala.epfl

import org.scalacheck._
import org.scalacheck.Prop._
import Arbitrary.arbitrary

import scala.collection.mutable.StringBuilder
import scala.util.matching.Regex
import scala.util.parsing.combinator._

/*
 * TODO:
 * -- Generalize regular expression generator
 * -- Union/Intersection/Negation/Ranges of character classes
 * -- Method to collect stats on depth and breadth of regexes
 * -- Reluctant/Possessive quantifiers, only greedy generated for now
 * -- Look ahead/look behind?
 * -- ***Figure out which generated strings are not accepted***
 *    currently wraps propositions in implication ensuring all generated
 *    strings are actually in the RE's language.
 */

object RegexParsersTest extends Properties("RegexParsers") with RegexParsers {
  
  // We want to be able to match whitespace as well.
  override val skipWhitespace = false
  
  lazy val acceptAnyString: Parser[String] = ".*".r
  
  // Characters that have special meaning in character classes.
  // These must be escaped if treated as literals.
  val ccSpecialChars = """[].&-$@!#+\"{}<|^""" toList
  val funnyWSMap = Map('\t' -> "\\t", '\f' -> "\\f",
		       '\n' -> "\\n", '\r' -> "\\r",
		       11.toChar -> "\\x0B")
  val specialChars = """[].&$&^\?(){}|+*""" toList
  
  // The set of all printable ascii characters.  Ignoring new-lines, having
  // trouble with those.
  val allPrAscChars = (9 :: List.range(32, 127)).
		      map (_.toChar) toSet
  //val allPrAscChars = (((9 until 14) toList) ::: List.range(32, 127)).
  //	      map (_.toChar) toSet
  
  // Predefined character classes.
  val dAscChars = (48 until 58) map(_.toChar) toSet
  val upperAscChars = (65 until 91) map(_.toChar) toSet
  val lowerAscChars = (97 until 123) map(_.toChar) toSet
  //val sAscChars = (32 :: ((9 until 14) toList)) map (_.toChar) toSet
  val sAscChars = List(9, 32) map (_.toChar) toSet
  lazy val wAscChars = dAscChars ++ upperAscChars ++ lowerAscChars + '_'
  lazy val DAscChars = allPrAscChars -- dAscChars
  lazy val WAscChars = allPrAscChars -- wAscChars
  lazy val SAscChars = allPrAscChars -- sAscChars
  
  val predefMap = Map('any -> (".", allPrAscChars),
		      'digit -> ("\\d", dAscChars),
		      'word -> ("\\w", wAscChars),
		      'wSpace -> ("\\s", sAscChars),
		      'nonDigit -> ("\\D", DAscChars),
		      'nonWord -> ("\\W", WAscChars),
		      'nonWSpace -> ("\\S", SAscChars))
  
  // Valid unary operations for unary operations.
  //val unOps = List('star, 'plus, 'qMark)
  val unOps = Map('star -> "*", 'plus -> "+", 'qMark -> "?")
  
  // Valid binary operations for regular expressions.
  val binOps = List('cat, 'or)
  
  /*
   * Enumeration of forms of character classes.  Note that for negation
   * I consider the set of all printable ascii characters less than
   * code 127 and whitespace characters as the entire set of characters.
   */
  sealed abstract class CharClass extends RegExpAbs
  //case class Range(s: Int, e: Int) extends CharClass
  //case class Neg(c: CharClass) extends CharClass
  //case class CCUnion(ccs: List[CharClass]) extends CharClass
  //case class CCIntersection(ccs: List[CharClass]) extends CharClass
  
  // An arbitrary subset of allPrAscChars.
  case class CCArbitrary(charSet: Set[Char]) extends CharClass
  // Single character
  case class CCLiteral(c: Char) extends CharClass
  // Predefine character class
  case class CCPredef(s: Symbol) extends CharClass
  
  /*
   * Unary operation over regular expressions.
   */
  case class ReUnOp(op: Symbol, exp: RegExpAbs) extends RegExpAbs
  
  /*
   * Combines 2 or more regular expressions by folding these expressions
   * with the binary operator.
   */
  case class ReBinOp(op: Symbol, exps: Seq[RegExpAbs]) extends RegExpAbs
  
  /*
   * Attempt at a relatively comprehensive regular expression generator.
   * Character classes are expressed as arbitrary subsets of the set of
   * printable ascii characters.  Does not cover negation or intersection.
   */
  sealed abstract class RegExpAbs {
    override def toString : String = this match {
	case CCArbitrary(charSet) => {
	  val strSet = charSet.map(c =>
			     if (ccSpecialChars contains c) "\\" + c
			     else if (funnyWSMap contains c) funnyWSMap(c)
			     else "" + c)
	  charSet.size match {
	    case 0 => ""
	    case _ => "[%s]".format(strSet mkString)
	  }
	}
	case CCLiteral(c) =>
	  if (specialChars contains c) "\\" + c
	  else if (funnyWSMap contains c) funnyWSMap(c)
	  else "" + c
	case CCPredef(s) => predefMap(s)._1
	case ReUnOp(op, exp) =>
	  exp.toString match {
	    case "" => ""
	    case str => 
	      exp match {
		case _:CharClass => "%s%s" format(str, unOps(op))
		case _ => "(%s)%s" format(str, unOps(op))
	      }
	}
	case ReBinOp(op, exps) => exps match {
	  case Nil => ""
	  case h::t => op match {
	    case 'cat => ((exps filter(_.toString != "")) 
			  map (_.toString)) mkString
	    case 'or => ((exps filter(_.toString != ""))
			 map (_.toString)) mkString("(", "|", ")")
	    case _ => throw new java.lang.Exception
				("Unrecognized operation " + op)
	  }
	}
    }
    
    def toPrettyString(indent: Int): String = this match {
      case CCArbitrary(cSet) => {
	  val strSet = cSet.map(c =>
			     if (ccSpecialChars contains c) "\\" + c
			     else if (funnyWSMap contains c) funnyWSMap(c)
			     else "" + c)
	  cSet.size match {
	    case 0 => " "*indent + "CCArbitrary: \"\""
	    case _ => " "*indent +
		      "CCArbitrary: \"[%s]\"".format(strSet mkString)
	  }
      }
      case CCPredef(s) => " "*indent + 
		      "CCPredef: \"%s\"".format(predefMap(s)._1)
      case CCLiteral(c) => 
	  if (specialChars contains c)
	      " "*indent + "CCLiteral: \"\\" + c + "\""
	  else if (funnyWSMap contains c) " "*indent +
	      "CCLiteral: \"" + funnyWSMap(c) + "\""
	  else " "*indent + "CCLiteral: \"" + c + "\""
      case ReUnOp(op, exp) => " "*indent + op.toString + ":\n" +
			exp.toPrettyString(indent+2) + "\n"
      case ReBinOp(op, exps) => " "*indent + op.toString + ":\n" + 
			exps.map(_.toPrettyString(indent+2)).mkString + "\n"
    }
    
    /*
     * Converts this regex abstraction to a Scala regular expression.
     */
    def r : Regex = this.toString.r
    
    /*
     * Returns a generator for strings accepted by this regex.
     */
    def getAcceptStrGen : Gen[String] = this match {
	case CCArbitrary(charSet) =>
	  Gen.pick(1, ((charSet.map(_.toString)).toList)).map(_.head)
	case CCLiteral(c) => Gen.value(c toString)
	case CCPredef(s) => 
	  Gen.pick(1, (predefMap(s)._2.map(_.toString))).map(_.head)
	case ReUnOp(op, exp) => op match {
	  case 'star => Gen.listOf(exp.getAcceptStrGen) map (_ mkString)
	  case 'plus => Gen.listOf1(exp.getAcceptStrGen) map (_ mkString)
	  case 'qMark => Gen.oneOf(Gen.value(""), exp.getAcceptStrGen)
	  case _ => throw new java.lang.Exception
				("Unrecognized operation " + op)
	}
	case ReBinOp(op, exps) => op match {
	  case 'cat => (exps.foldLeft(Gen.value(""))
	       ((gen: Gen[String], exp: RegExpAbs) =>
		   gen.combine(exp.getAcceptStrGen)((u, v) =>
		     v match {
		       case Some(w) => u match {
			 case Some(x) => Some(x + w)
			 case None => v
		       }
		       case None => u
		     })))
	  case 'or => {
	    val strGens = exps map((exp: RegExpAbs) => (1, exp.getAcceptStrGen))
	    Gen.frequency(strGens: _*)
	    // Initially tried:
	    // Gen.oneOf(exps map(_.getAcceptStrGen))
	    // but compiler threw a fit (type mismatch, and when Gen.oneOf
	    // was parameterized, claimed that it the argument was still not
	    // of the right type.)
	  }
	  case _ => throw new java.lang.Exception
				("Unrecognized operation " + op)
	}
    }
    
    /*
     * Returns the number of character classes in the leaves of this regex.
     */
    def breadth: Int = this match {
      case cc: CharClass => 1
      case ReUnOp(_, exp) => exp breadth
      case ReBinOp(_, exps) => (exps map (_.breadth)).
	  foldLeft(0) ((a:Int, b:Int) => a+b)
    }
    
    /*
     * Returns how deep this regex is.
     */
    def depth: Int = this match {
      case cc: CharClass => 0
      case ReUnOp(_, exp) => 1 + exp.depth
      case ReBinOp(_, exps) => 1 + (exps map (_.depth)).max
    }
  }
  
  lazy val reCCSetGen : Gen[CharClass] =
      Gen.someOf(allPrAscChars).map[CharClass](
	  (ccSet: Seq[Char]) =>
	    CCArbitrary(Set(ccSet.toList: _*)))
  
  lazy val reCCPredefGen : Gen[CharClass] =
    Gen.pick(1, predefMap keySet).map[CharClass](
      (ss: Seq[Symbol]) => CCPredef(ss head))
  
  lazy val reCCLiteralGen : Gen[CharClass] =
    Gen.pick(1, allPrAscChars).map[CharClass](
      (cs: Seq[Char]) => CCLiteral(cs head))
  
  /*
   * Only generates literals and pre-defined character classes for now.
   */
  lazy val reCCGen : Gen[CharClass] =
    Gen.frequency((10, Gen.lzy(reCCLiteralGen)), (1, Gen.lzy(reCCPredefGen)))
  
  /*
   * Generator for unary operations.
   */
  def reUnOpGen(depth:Int) : Gen[ReUnOp] = for {
    op <- Gen.oneOf(Gen.value('star), Gen.value('plus), Gen.value('qMark))
    reAscExp <- Gen.lzy(reAscExpGen(depth-1))
  } yield ReUnOp(op, reAscExp)
  
  /*
   * Generator for binary operations.
   */
  def reBinOpGen(depth:Int) : Gen[ReBinOp] =
    for {
      op <- Gen.frequency((1, Gen.value('cat)), (1, Gen.value('or)))
      reAscExpList <- Gen.listOf(Gen.lzy(reAscExpGen(depth-1)))
    } yield ReBinOp(op, reAscExpList)
  
  // Generates a random regular expression.  This object can be used to
  // generate a string representation of the regex as well as a generator
  // of strings accepted by this regex.
  def reAscExpGen(depth:Int) : Gen[RegExpAbs] =
      if (depth>0) Gen.frequency((4, Gen.lzy(reBinOpGen(depth-1))),
				 (4, Gen.lzy(reCCGen)),
				 (1, Gen.lzy(reUnOpGen(depth-1))))
      else Gen.lzy(reCCGen)
  
  /*
   * Constrains the depth of regular expressions generated.
   */
  implicit def arbRegex: Arbitrary[RegExpAbs] = Arbitrary(reAscExpGen(2))
  
  /*
   * Shrinker for regular expression abstractions.
   */
  implicit def shrinkRegex: Shrink[RegExpAbs] = Shrink {
    re:RegExpAbs =>
      re match {
	case CCArbitrary(cSet) => 
	  for(cSet1 <- Shrink.shrink(cSet)) yield CCArbitrary(cSet1)
	case CCLiteral(c) => for (i <- Stream(1)) yield CCArbitrary(Set())
	case CCPredef(s) => for (i <- Stream(1)) yield CCArbitrary(Set())
	//  for (ccSet <- Shrink.shrink(predefMap(s)._2))
	//    yield CCArbitrary(ccSet)
	case ReUnOp(op, exp) => 
	  (for (exp1 <- Shrink.shrink(exp))
	     yield List(ReUnOp(op, exp1), exp1)).flatten
	case ReBinOp(op, exps) => 
	  (for (exps1 <- Shrink.shrink(exps))
	     yield ReBinOp(op, exps1)).
	    append(
	      (for (exp <- exps) yield Shrink.shrink(exp)).toList.flatten)
      }
  }
  
  property(acceptAnyString.toString + " accepts all Strings") = Prop.forAll {
    a: String => {
      parseAll(acceptAnyString, a) match {
        case Success(res, _) => res == a
        case NoSuccess(_, _) => false
      }
    }
  }
  
  property("`literal` accepts any matching String") = Prop.forAll {
    a: String => {
      val literalParser = literal(a)
      parseAll(literalParser, a) match {
        case Success(res, _) => res == a
        case NoSuccess(_, _) => false
      }
    }
  }
  
  /*
   * The following two properties check the soundness of RegExpAbs.
   */
  
  property("Regex generator produces well-formed expressions.") =
    Prop.forAll {
      r: RegExpAbs => {
	try {
	  val re = r.r
	  true
	}
	catch {case _ => false}
      }
    }
  
  /*
   * This property does not necessarily hold.  For combinator properties,
   * check if both regular expressions accept their input strings, then
   * commence testing.
   */
  property("getAcceptStrGen only generates accepted strings") = Prop.forAll {
    r: RegExpAbs => {
      val strGen = r getAcceptStrGen
      val re = r.r
      Prop.forAllNoShrink(strGen) {
	s:String => {
	  parseAll(re, s) match {
	    case Success(res, _) => res==s
	    case NoSuccess(_, _) => false
	  }
	}
      }
    }
  }
  
  // Checks if a string is in the regex's language.
  def inLang(re: Regex, s: String): Boolean =
    parseAll(re, s) match {
        case Success(res, _) => true
	case NoSuccess(_, _) => false
    }
  
  def inLangAll(reTups: (Regex, String)*): Boolean = 
    reTups forall((reTup: (Regex, String)) => inLang(reTup._1, reTup._2))
  
  def reAllProp1[T <% Prop](prop: (Regex, String) => T): Prop = 
    Prop.forAll {
      r: RegExpAbs => {
	val strGen = r getAcceptStrGen
	val re = r.r
	Prop.forAll(strGen) {
	  (s: String) => (inLang(re, s) ==> prop(re, s))
	}
      }
    }
  
  // Universally quantified proposition regarding two regular 
  // expressions and the set of strings in each of their languages.
  def reAllProp2[T <% Prop](prop: (Regex, Regex, String, String) => T): Prop =
    Prop.forAll {
      (r1: RegExpAbs, r2: RegExpAbs) => {
	val (strGen1, strGen2) = (r1 getAcceptStrGen, r2 getAcceptStrGen)
	val (re1, re2) = (r1.r, r2.r)
	Prop.forAll(strGen1) {
	  (s1: String) =>
	  Prop.forAll(strGen2) {
	    (s2: String) =>
	      (inLangAll((re1, s1), (re2, s2)) ==> prop(re1, re2, s1, s2))
	  }
	}
      }
    }
  
  lazy val smallNonNegIntGen: Gen[Int] = Gen.choose(0, 100)
  
  def getRepGen(s: String, sep: String): Gen[String] = {
    for (n <- smallNonNegIntGen) yield List.fill(n)(s) mkString sep
  }
  
  property("""rep of regex accepts any repetition of string in its language,
	   if empty string is not in its language.""") =
    reAllProp1(
      (re: Regex, s: String) =>
      Prop.forAll(getRepGen(s, "")) {
	reps: String => {
          // Checks if empty string is in RE's language, to make sure
	  // an infinite sequence of empty strings isn't matched.
	  (!inLang(re, "") ==>
	    (parseAll(rep(re), reps) match {
	      case Success(_, _) => true
	      case NoSuccess(_, _) => false
	    })
	  )
	}
      })
  
  def amtConsumed(re: Regex, s: String): Int =
    parse(re, s) match {
      case Success(res, _) => res.length
      case NoSuccess(_, rest) => 0
    }
  
  property("""repN of regex accepts n repetitions of string in its language,
	   if regex does not match more than the original string""") =
    reAllProp1(
      (re: Regex, s: String) =>
	Prop.forAll(smallNonNegIntGen) {
	  n: Int =>
	    n>=0 ==> {
	      // Makes sure regex doesn't eat more than the original string.
	      (amtConsumed(re, List.fill(n)(s) mkString) <= s.length) ==>
		(parseAll(repN(n, re), List.fill(n)(s) mkString) match {
		  case Success(_, _) => true
		  case NoSuccess(_, _) => false
		})
	    }
	})
  
  property("repsep of regex accepts repetition of string in its language") =
    reAllProp1(
      (re: Regex, s: String) =>
      Prop.forAll(getRepGen(s, "~")) {
	reps: String => {
	  parseAll(repsep(re, "~"), reps) match {
	    case Success(_, _) => true
	    case NoSuccess(_, _) => false
	  }
	}
      })
  
  property("Or of regex accepts strings in either language") =
    reAllProp2(
      (re1: Regex, re2: Regex, s1: String, s2: String) =>
	(parseAll(re1 ||| re2, s1), parseAll(re1 ||| re2, s2)) match {
	  case (Success(_, _), Success(_, _)) => true
	  case _ => false
	})
  
  property("""Cat of regex languages accepted by ~ 
	     of regexes, if re1 not a prefix of re2.""") =
    reAllProp2(
      (re1: Regex, re2: Regex, s1: String, s2: String) =>
	((amtConsumed(re1, s2) == 0) ==>
	  (parseAll(re1 ~ re2, s1 + s2) match {
	    case Success(_, rest) => rest atEnd
	    case NoSuccess(_, _) => false
	  }))
      )
  
  property("""Cat of regex languages accepted by ~> of regexes
	     if re1 not a prefix of re2.""") =
    reAllProp2(
      (re1: Regex, re2: Regex, s1: String, s2:String) => {
	((amtConsumed(re1, s2) == 0) ==>
	  (parseAll(re1 ~> re2, s1 + s2) match {
	    case Success(res, _) => s2 endsWith res
	    case NoSuccess(_, _) => false
	  }))
      })
  
  property("""Cat of regex languages accepted by <~ of regexes
	   if re1 not a prefix of re2.""") =
    reAllProp2(
      (re1: Regex, re2: Regex, s1: String, s2:String) =>
	((amtConsumed(re1, s2) == 0) ==>
	  (parseAll(re1 <~ re2, s1 + s2) match {
	    case Success(res, _) => res startsWith s1
	    case NoSuccess(_, _) => false
	  })
	)
    )
  
  property("~ of two literal parsers accepts concatenation") =
    Prop.forAll {
    (a : String, b : String) => {
      val abParser = literal(a) ~ literal(b)
      parseAll(abParser, a +  b) match {
        case Success(_, rest) => rest atEnd
	case NoSuccess(_, _) => false
      }
    }
  }
  
  property("~> of two literal parsers accepts concatenation, returns RHS") =
    Prop.forAll {
    (a : String, b : String) => {
      val abRArgParser = literal(a) ~> literal(b)
      parseAll(abRArgParser, a + b) match {
        case Success(res, _) =>  res == b
	case NoSuccess(_, _) => false
      }
    }
  }
  
  property("<~ of two literal parsers accepts concatenation, returns LHS") =
    Prop.forAll {
    (a : String, b : String) => {
      val abLArgParser = literal(a) <~ literal(b)
      parseAll(abLArgParser, a + b) match {
        case Success(res, _) => res == a
        case NoSuccess(_, _) => false
      }
    }
  }
}
