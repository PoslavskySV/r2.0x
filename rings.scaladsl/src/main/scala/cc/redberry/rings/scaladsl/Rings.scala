package cc.redberry.rings.scaladsl

import java.util.Objects

import cc.redberry.rings
import cc.redberry.rings.poly.multivar.MonomialOrder
import cc.redberry.rings.{poly, _}

import scala.language.{existentials, implicitConversions, postfixOps}

/**
  * Simple wrapper around [[Ring]] used to unify PolynomialRing and Ring
  *
  * @param theRing the [[Ring]]
  **/
sealed class Ring[E](val theRing: rings.Ring[E]) extends ToStringSupport[E] with ElementParser[E] with RingSupport[E] {

  override def ringEv(ev: E): Ring[E] = this

  /**
    * Element type
    */
  final type ElementType = E

  /**
    * @inheritdoc
    **/
  override final def toString(element: E): String = _show(element)

  /**
    * @inheritdoc
    **/
  override def parse(string: String): E = theRing parse string

  /** Parse */
  final def apply(string: String): E = parse(string)

  final def apply(int: Int): E = theRing.valueOf(int)

  final def apply(int: BigInt): E = theRing.valueOfBigInteger(int)

  final def apply(int: IntZ): E = theRing.valueOfBigInteger(int)

  final def apply(a: String, b: String): (E, E) = (parse(a), parse(b))

  final def apply(a: String, b: String, c: String): (E, E, E)
  = (parse(a), parse(b), parse(c))

  final def apply(a: String, b: String, c: String, d: String): (E, E, E, E)
  = (parse(a), parse(b), parse(c), parse(d))

  final def apply(a: String, b: String, c: String, d: String, e: String): (E, E, E, E, E)
  = (parse(a), parse(b), parse(c), parse(d), parse(e))

  /**
    * @inheritdoc
    **/
  override def toString: String = Objects.toString(theRing)


  /** element class  */
  private lazy val eClass: Class[_ <: E] = theRing.getZero.getClass

  /**
    * Reflection: determines whether is element of this
    */
  def isElement(e: Any): Boolean = eClass isAssignableFrom e.getClass

  /**
    * Casts e to element of this
    */
  final def element(e: Any): E = e.asInstanceOf[E]

  protected[scaladsl] def _show(obj: Any): String = Objects.toString(obj)

  /**
    * Pretty toString
    */
  final def show(arg: Any): String = arg match {
    case obj: Array[_] =>
      obj.map(show).mkString("[", ",", "]")
    case obj: Product =>
      obj.productIterator.map(show).mkString("(", ",", ")")
    case obj: Traversable[_] =>
      obj.map(show).toString
    case any@_ => _show(any)
  }
}

/**
  * Ring of rationals
  */
final case class Frac[E](ring: Ring[E]) extends Ring[Rational[E]](rings.Rings.Frac(scaladsl.ringMethods(ring))) {
  private val rationalsDomain: rings.Rationals[E] = theRing.asInstanceOf[rings.Rationals[E]]

  /**
    * @inheritdoc
    **/
  override def parse(string: String): Rational[E] = rationalsDomain.parse(ring, string)

  /**
    * Pretty toString
    */
  override def _show(obj: Any): String = obj match {
    case rat: Rational[E] =>
      rat.toString(ring)
    case element => ring.show(element)
  }
}

/**
  * Base class for polynomial rings
  *
  * @param theRing   the [[PolynomialRing]]
  * @param variables polynomial variables
  * @tparam E coefficient type
  */
abstract class PolynomialRing[Poly <: IPolynomial[Poly], E]
(override val theRing: poly.PolynomialRing[Poly],
 val variables: Array[String]) extends Ring[Poly](theRing) {

  /**
    * Type of coefficients
    */
  final type CoefficientType = E

  /**
    * Type of polynomials
    */
  final type PolyType = ElementType

  /**
    * The coefficient ring
    */
  def cfRing: Ring[E]

  /**
    * Reflection: determines whether is element of this
    */
  override def isElement(e: Any): Boolean
  = super.isElement(e) && e.asInstanceOf[Poly].sameCoefficientRingWith(theRing.getZero)

  /**
    * Parse polynomial
    */
  override def parse(string: String): Poly = theRing.parse(string, variables)

  private lazy val toStringSupport: ToStringSupport[Any] = new ToStringSupport[Any] {
    override def toString(element: Any): String = show(element)
  }

  /**
    * To string
    */
  override def _show(obj: Any): String = obj match {
    case el: E if cfRing.isElement(el) => cfRing.show(el)
    case obj: FactorDecomposition[PolyType] =>
      obj.toString(toStringSupport.asInstanceOf[ToStringSupport[PolyType]])
    case wv: WithVariables => show(wv)
    case _ => super._show(obj)
  }

  /**
    * String representation of polynomial from this ring
    */
  protected[scaladsl] def show(obj: WithVariables): String = obj match {
    case fct: FactorDecomposition[Poly] => fct.toString(this)
    case el if isElement(el) => el.toString(variables)
    case _ => obj.toString()
  }

  /**
    * String representation of a seq of polynomials
    */
  final def show(list: Traversable[_]): String
  = list.map {
    case wv: WithVariables => show(wv)
    case p => p.toString
  }.toString

  /**
    * Index of variable with specified string representation
    */
  final def index(variable: String): Int = variables.indexOf(variable)

  /**
    * Index of variable with specified string representation
    */
  final def variable(variable: String): Int = index(variable)

  /**
    * String representation of this ring
    */
  override def toString: String = theRing.toString(variables)

  /**
    * The first variable
    */
  final lazy val `x`: Poly = theRing.variable(0)

  /**
    * The second variable
    */
  final lazy val `y`: Poly = theRing.variable(1)

  /**
    * The third variable
    */
  final lazy val `z`: Poly = theRing.variable(2)

  /**
    * Shortcut for /% operation
    */
  protected[scaladsl] final def divRem(a: Poly, b: Poly): (Poly, Poly) = {
    val qd = theRing.divideAndRemainder(a, b)
    if (qd == null)
      throw new ArithmeticException(s"not divisible with remainder: ${this show a } / ${this show b }")
    (qd(0), qd(1))
  }

  final def apply(value: E): Poly = getConstant(value)

  /**
    * Constant polynomial with specified value
    */
  def getConstant(value: E): Poly

  /**
    * Add coefficient ring element
    */
  def addConstant(poly: Poly, el: E): Poly

  /**
    * Subtract coefficient ring element
    */
  def subtractConstant(poly: Poly, el: E): Poly

  /**
    * Multiply by coefficient ring element
    */
  def multiplyConstant(poly: Poly, el: E): Poly

  /**
    * Divide by coefficient ring element
    */
  def divideConstant(poly: Poly, el: E): Poly

  /**
    * Divide by coefficient ring element
    */
  def divideAndRemainder(poly: Poly, el: E): (Poly, Poly)

  /**
    * Value of integer in coefficient ring
    */
  def cfValue(i: Int): E

  /**
    * Constant coefficient
    */
  def cc(poly: Poly): E

  /**
    * Leading coefficient
    */
  def lc(poly: Poly): E
}

object PolynomialRing {
  def apply[Poly <: IPolynomial[Poly], E](factory: Poly): PolynomialRing[Poly, E] = factory match {
    case p: UnivariatePolynomialZp64 => UnivariateRingZp64(p.ring, WithVariables.defaultVars(1)(0)).asInstanceOf[PolynomialRing[Poly, E]]
    case p: UnivariatePolynomial[E forSome {type E}] => UnivariateRing(p.ring, WithVariables.defaultVars(1)(0)).asInstanceOf[PolynomialRing[Poly, E]]
    case p: MultivariatePolynomialZp64 => MultivariateRingZp64(p.ring, WithVariables.defaultVars(p.nVariables), p.ordering).asInstanceOf[PolynomialRing[Poly, E]]
    case p: MultivariatePolynomial[E forSome {type E}] => MultivariateRing(p.ring, WithVariables.defaultVars(p.nVariables), p.ordering).asInstanceOf[PolynomialRing[Poly, E]]
    case _ => ???
  }
}

/**
  * Ring of univariate polynomials
  *
  * @param theRing  the [[PolynomialRing]]
  * @param variable the variable
  */
sealed abstract class IUnivariateRing[Poly <: IUnivariatePolynomial[Poly], E]
(override val theRing: poly.PolynomialRing[Poly],
 val variable: String) extends PolynomialRing[Poly, E](theRing, Array(variable)) {
  /**
    * Evaluate poly at a given point
    */
  def eval(poly: Poly, point: E): E

  /**
    * i-th coefficient
    */
  def at(poly: Poly, index: Int): E = cc(poly.getAsPoly(index))
}

/**
  * Galois field with prime base in a range of `(0, 2^63)`
  *
  * @param theRing  the [[rings.poly.FiniteField]]
  * @param variable the variable of univariate polynomials representing this Galois field
  */
final case class GaloisField64
(override val theRing: rings.poly.FiniteField[UnivariatePolynomialZp64], override val variable: String)
  extends IUnivariateRing[UnivariatePolynomialZp64, Long](theRing, variable) {

  /**
    * The coefficient ring
    */
  override val cfRing: Ring[Long] = theRing.factory().ring

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: Long): UnivariatePolynomialZp64 = theRing.valueOf(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().divide(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: UnivariatePolynomialZp64, el: Long): (UnivariatePolynomialZp64, UnivariatePolynomialZp64)
  = divRem(poly, theRing.valueOf(el))

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): Long = i.asInstanceOf[Long]

  /**
    * Evaluate poly at a given point
    */
  override def eval(poly: UnivariatePolynomialZp64, point: Long): Long = poly.evaluate(point)

  /**
    * Constant coefficient
    */
  override def cc(poly: UnivariatePolynomialZp64): Long = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: UnivariatePolynomialZp64): Long = poly.lc()
}

/**
  * Galois field with arbitrary prime base
  *
  * @param theRing  the [[rings.poly.FiniteField]]
  * @param variable the variable of univariate polynomials representing this Galois field
  */
final case class GaloisField[E]
(override val theRing: rings.poly.FiniteField[UnivariatePolynomial[E]], override val variable: String,
 private val ringOption: Option[UnivariateRing[E]] = None)
  extends IUnivariateRing[UnivariatePolynomial[E], E](theRing, variable) {

  /**
    * The coefficient ring
    */
  override val cfRing: Ring[E] = theRing.factory().ring

  /**
    * @inheritdoc
    */
  override def parse(string: String): UnivariatePolynomial[E] = ringOption match {
    case Some(ring) => theRing.valueOf(theRing.factory().parsePoly(string, ring.coefficientDomain, variable))
    case None => super.parse(string)
  }

  /**
    * @inheritdoc
    */
  override def show(obj: WithVariables): String = ringOption match {
    case Some(ring) =>
      obj match {
        case poly: UnivariatePolynomial[E] => poly.toString(ring.coefficientDomain, variable)
        case cfx if ringOption.isDefined && ringOption.get.isElement(cfx) => ringOption.get.show(cfx)
        case _ => super.show(obj)
      }
    case None => super.show(obj)
  }

  /**
    * @inheritdoc
    */
  override val toString: String = ringOption match {
    case Some(ring) => theRing.toString(ring.coefficientDomain.toString, this, variables)
    case None => super.toString
  }

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: E): UnivariatePolynomial[E] = theRing.factory().createConstant(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().divideExact(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: UnivariatePolynomial[E], el: E): (UnivariatePolynomial[E], UnivariatePolynomial[E])
  = divRem(poly, poly.createConstant(el))

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): E = cfRing.valueOf(i.asInstanceOf[Long])

  /**
    * Evaluate poly at a given point
    */
  override def eval(poly: UnivariatePolynomial[E], point: E): E = poly.evaluate(point)

  /**
    * Constant coefficient
    */
  override def cc(poly: UnivariatePolynomial[E]): E = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: UnivariatePolynomial[E]): E = poly.lc()
}

object GF {
  /**
    * Create Galois field with cardinality `modulus ^ exponent` represented by univariate polynomials with
    * specified variable
    */
  def apply(modulus: Long, exponent: Int, variable: String = "z")
  = GaloisField64(rings.Rings.GF(modulus, exponent), variable)

  /**
    * Create Galois field from the specified irreducible polynomial and represented by univariate polynomials with
    * specified variable
    */
  def apply(irreducible: UnivariatePolynomialZp64, variable: String)
  = GaloisField64(rings.Rings.GF(irreducible), variable)

  /**
    * Create Galois field with cardinality `modulus ^ exponent` represented by univariate polynomials with
    * specified variable
    */
  def apply(modulus: IntZ, exponent: Int, variable: String)
  = GaloisField[IntZ](rings.Rings.GF(modulus, exponent), variable)

  /**
    * Create Galois field from the specified irreducible polynomial and represented by univariate polynomials with
    * specified variable
    */
  def apply[E](irreducible: UnivariatePolynomial[E], variable: String)
  = GaloisField[E](rings.Rings.GF(irreducible), variable)

  /**
    * Create Galois field from the specified irreducible polynomial and represented by univariate polynomials with
    * specified variable
    */
  def apply[E](irreducible: UnivariatePolynomial[E], univariateRing: UnivariateRing[E], variable: String)
  = GaloisField[E](rings.Rings.GF(irreducible), variable, Some(univariateRing))
}

/**
  * Ring of Zp[x] polynomials
  *
  * @param coefficientDomain coefficient ring
  * @param variable          variable
  */
final case class UnivariateRingZp64 private(override val variable: String, coefficientDomain: IntegersZp64)
  extends IUnivariateRing[UnivariatePolynomialZp64, Long](rings.Rings.UnivariateRingZp64(coefficientDomain), variable) {
  val modulus: Long = coefficientDomain.modulus

  /**
    * The coefficient ring
    */
  override val cfRing: Ring[Long] = coefficientDomain

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: Long): UnivariatePolynomialZp64 = theRing.valueOf(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: UnivariatePolynomialZp64, el: Long): UnivariatePolynomialZp64
  = poly.copy().divide(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: UnivariatePolynomialZp64, el: Long): (UnivariatePolynomialZp64, UnivariatePolynomialZp64)
  = (poly.copy().divide(el), poly.createZero())

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): Long = i.asInstanceOf[Long]

  /**
    * Evaluate poly at a given point
    */
  override def eval(poly: UnivariatePolynomialZp64, point: Long): Long = poly.evaluate(point)

  /**
    * Constant coefficient
    */
  override def cc(poly: UnivariatePolynomialZp64): Long = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: UnivariatePolynomialZp64): Long = poly.lc()
}

object UnivariateRingZp64 {
  /**
    * Zp[variable] with specified modulus
    */
  def apply(modulus: Long, variable: String): UnivariateRingZp64 = new UnivariateRingZp64(variable, new IntegersZp64(modulus))

  /**
    * Zp[variable] with specified coefficient ring (Zp)
    */
  def apply(domain: IntegersZp64, variable: String) = new UnivariateRingZp64(variable, domain)
}

/**
  * Ring of univariate polynomials over generic domains
  *
  * @param coefficientDomain coefficient ring
  * @param variable          variable
  */
final case class UnivariateRing[E](coefficientDomain: Ring[E], override val variable: String)
  extends IUnivariateRing[UnivariatePolynomial[E], E](rings.Rings.UnivariateRing(coefficientDomain.theRing), variable) {

  /**
    * The coefficient ring
    */
  override val cfRing: Ring[E] = coefficientDomain

  /**
    * @inheritdoc
    */
  override def show(obj: WithVariables): String = obj match {
    case poly: UnivariatePolynomial[E] => poly.toString(coefficientDomain, variable)
    case cfx if coefficientDomain.isElement(cfx) => coefficientDomain._show(cfx)
    case _ => super.show(obj)
  }

  /**
    * @inheritdoc
    */
  override def parse(string: String): UnivariatePolynomial[E] = theRing.factory().parsePoly(string, coefficientDomain, variable)

  /**
    * @inheritdoc
    */
  override val toString: String = theRing.toString(coefficientDomain.toString, variables)

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: E) = theRing.factory().createConstant(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: UnivariatePolynomial[E], el: E): UnivariatePolynomial[E]
  = poly.copy().divideExact(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: UnivariatePolynomial[E], el: E): (UnivariatePolynomial[E], UnivariatePolynomial[E])
  = divRem(poly, poly.createConstant(el))

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): E = coefficientDomain.theRing.valueOf(i.asInstanceOf[Long])

  /**
    * Evaluate poly at a given point
    */
  override def eval(poly: UnivariatePolynomial[E], point: E): E = poly.evaluate(point)

  /**
    * Constant coefficient
    */
  override def cc(poly: UnivariatePolynomial[E]): E = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: UnivariatePolynomial[E]): E = poly.lc()
}

/**
  * Ring of multivariate polynomials
  *
  * @param theRing   the [[PolynomialRing]]
  * @param variables the variables
  */
sealed abstract class IMultivariateRing[Term <: DegreeVector[Term], Poly <: AMultivariatePolynomial[Term, Poly], E]
(override val theRing: poly.PolynomialRing[Poly],
 variables: Array[String],
 ordering: Ordering) extends PolynomialRing[Poly, E](theRing, variables) {
  /**
    * The type of monomials
    */
  type MonomialType = Term

  /**
    * Evaluate poly for given variable
    */
  def eval(poly: Poly, variable: Int, value: E): Poly

  //    /**
  //      * Evaluate poly for given variables
  //      */
  //    def eval(poly: Poly, variables: Array[Int], values: Array[E]): Poly
}


/**
  * Zp[variables] with specified modulus
  *
  * @param coefficientDomain coefficient ring
  */
final case class MultivariateRingZp64
(coefficientDomain: IntegersZp64, override val variables: Array[String], ordering: Ordering)
  extends IMultivariateRing[MonomialZp64, MultivariatePolynomialZp64, Long](
    rings.Rings.MultivariateRingZp64(variables.length, coefficientDomain, ordering), variables, ordering) {
  /**
    * The coefficient ring
    */
  override val cfRing: Ring[Long] = coefficientDomain

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: Long): MultivariatePolynomialZp64 = theRing.valueOf(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: MultivariatePolynomialZp64, el: Long): MultivariatePolynomialZp64
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: MultivariatePolynomialZp64, el: Long): MultivariatePolynomialZp64
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: MultivariatePolynomialZp64, el: Long): MultivariatePolynomialZp64
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: MultivariatePolynomialZp64, el: Long): MultivariatePolynomialZp64
  = poly.copy().divide(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: MultivariatePolynomialZp64, el: Long): (MultivariatePolynomialZp64, MultivariatePolynomialZp64)
  = (poly.copy().divide(el), poly.createZero())

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): Long = i.asInstanceOf[Long]

  /**
    * Evaluate poly for given variable
    */
  override def eval(poly: MultivariatePolynomialZp64, variable: Int, value: Long): MultivariatePolynomialZp64
  = poly.evaluate(variable, value)

  /**
    * Constant coefficient
    */
  override def cc(poly: MultivariatePolynomialZp64): Long = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: MultivariatePolynomialZp64): Long = poly.lc()
}

object MultivariateRingZp64 {
  /**
    * Zp[variables] with specified modulus, variables and ordering
    */
  def apply(modulus: Long, variables: Array[String], ordering: Ordering): MultivariateRingZp64
  = MultivariateRingZp64(new IntegersZp64(modulus), variables, ordering)

  /**
    * Zp[variables] with specified modulus, variables and default ordering (LEX)
    */
  def apply(modulus: Long, variables: Array[String]): MultivariateRingZp64
  = MultivariateRingZp64(new IntegersZp64(modulus), variables, MonomialOrder.LEX)
}

/**
  * Ring of multivariate polynomials over generic domains
  *
  * @param coefficientDomain coefficient ring
  */
final case class MultivariateRing[E]
(coefficientDomain: Ring[E], override val variables: Array[String], ordering: Ordering)
  extends IMultivariateRing[Monomial[E], MultivariatePolynomial[E], E](
    rings.Rings.MultivariateRing(variables.length, scaladsl.ringMethods(coefficientDomain), ordering), variables, ordering) {
  /**
    * The coefficient ring
    */
  override val cfRing: Ring[E] = coefficientDomain

  /**
    * @inheritdoc
    */
  override def show(obj: WithVariables): String = obj match {
    case poly: MultivariatePolynomial[E] => poly.toString(coefficientDomain, variables)
    case el if coefficientDomain.isElement(el) => coefficientDomain._show(el)
    case _ => super.show(obj)
  }

  /**
    * @inheritdoc
    */
  override def parse(string: String): MultivariatePolynomial[E] = theRing.factory().parsePoly(string, coefficientDomain, variables)

  /**
    * @inheritdoc
    */
  override val toString: String = theRing.toString(coefficientDomain.toString, variables)

  /**
    * Constant polynomial with specified value
    */
  override def getConstant(value: E) = theRing.factory().createConstant(value)

  /**
    * Add coefficient ring element
    */
  override def addConstant(poly: MultivariatePolynomial[E], el: E): MultivariatePolynomial[E]
  = poly.copy().add(el)

  /**
    * Subtract coefficient ring element
    */
  override def subtractConstant(poly: MultivariatePolynomial[E], el: E): MultivariatePolynomial[E]
  = poly.copy().subtract(el)

  /**
    * Multiply by coefficient ring element
    */
  override def multiplyConstant(poly: MultivariatePolynomial[E], el: E): MultivariatePolynomial[E]
  = poly.copy().multiply(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideConstant(poly: MultivariatePolynomial[E], el: E): MultivariatePolynomial[E]
  = poly.copy().divideExact(el)

  /**
    * Divide by coefficient ring element
    */
  override def divideAndRemainder(poly: MultivariatePolynomial[E], el: E): (MultivariatePolynomial[E], MultivariatePolynomial[E])
  = divRem(poly, poly.createConstant(el))

  /**
    * Value of integer in coefficient ring
    */
  override def cfValue(i: Int): E = coefficientDomain.valueOf(i.asInstanceOf[Long])

  /**
    * Evaluate poly for given variable
    */
  override def eval(poly: MultivariatePolynomial[E], variable: Int, value: E): MultivariatePolynomial[E]
  = poly.evaluate(variable, value)

  /**
    * Constant coefficient
    */
  override def cc(poly: MultivariatePolynomial[E]): E = poly.cc()

  /**
    * Leading coefficient
    */
  override def lc(poly: MultivariatePolynomial[E]): E = poly.cc()
}

object MultivariateRing {
  /**
    * Zp[variables] with specified modulus, variables and default ordering (LEX)
    */
  def apply[E](coefficientDomain: Ring[E], variables: Array[String]): MultivariateRing[E]
  = MultivariateRing[E](coefficientDomain, variables, MonomialOrder.LEX)
}

