package cc.redberry.rings;

import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.*;
import cc.redberry.rings.poly.MultivariateRing;
import cc.redberry.rings.poly.PolynomialRing;
import cc.redberry.rings.poly.UnivariateRing;
import cc.redberry.rings.poly.multivar.*;
import cc.redberry.rings.poly.univar.UnivariateDivision;
import cc.redberry.rings.poly.univar.UnivariateInterpolation.InterpolationZp64;
import cc.redberry.rings.poly.univar.UnivariatePolynomial;
import cc.redberry.rings.poly.univar.UnivariatePolynomialZ64;
import cc.redberry.rings.poly.univar.UnivariatePolynomialZp64;
import cc.redberry.rings.primes.BigPrimes;
import cc.redberry.rings.primes.SmallPrimes;
import org.apache.commons.math3.random.Well44497b;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.IntStream;

import static cc.redberry.rings.Rings.*;
import static cc.redberry.rings.poly.PolynomialMethods.*;
import static cc.redberry.rings.poly.multivar.MultivariateGCD.*;
import static cc.redberry.rings.poly.multivar.MultivariateGCD.ZippelGCDInZ;
import static cc.redberry.rings.poly.univar.IrreduciblePolynomials.*;
import static cc.redberry.rings.poly.univar.UnivariateGCD.*;
import static cc.redberry.rings.poly.univar.UnivariateGCD.ModularGCD;
import static cc.redberry.rings.poly.univar.UnivariateSquareFreeFactorization.SquareFreeFactorization;

/**
 * @author Stanislav Poslavsky
 * @since 1.0
 */
public class Examples {

    @Test
    public void name() throws Exception {
        // when parsing "x" will be considered as the "first variable"
        // and "y" as "the second" => in the result the particular
        // names "x" and "y" are erased
        MultivariatePolynomial<BigInteger> poly1 = MultivariatePolynomial.parse("x^2 + x*y", "x", "y");
        // parse the same polynomial but using "a" and "b" instead of "x" and "y"
        MultivariatePolynomial<BigInteger> poly2 = MultivariatePolynomial.parse("a^2 + a*b", "a", "b");
        // polynomials are equal (no matter which variable names were used when parsing)
        assert poly1.equals(poly2);
        // degree in the first variable
        assert poly1.degree(0) == 2;
        // degree in the second variable
        assert poly1.degree(1) == 1;

        // this poly differs from poly2 since now "a" is "the second"
        // variable and "b" is "the first"
        MultivariatePolynomial<BigInteger> poly3 = MultivariatePolynomial.parse("a^2 + a*b", "b", "a");
        assert !poly3.equals(poly2);
        // swap the first and the second variables and the result is equal to poly2
        assert AMultivariatePolynomial.swapVariables(poly3, 0, 1).equals(poly2);


        // the default toString() will use the default
        // variables "a", "b", "c"  and so on (alphabetical)
        // the result will be "a*b + a^2"
        System.out.println(poly1);
        // specify which variable names use for printing
        // the result will be "x*y + x^2"
        System.out.println(poly1.toString(new String[]{"x", "y"}));
        // the result will be "y*x + y^2"
        System.out.println(poly1.toString(new String[]{"y", "x"}));
    }

    @Test
    public void test3() throws Exception {
        // parse polynomials
        UnivariatePolynomial
                p1 = UnivariatePolynomial.parse("x", Z),
                p2 = UnivariatePolynomial.parse("x^2", Z),
                p3 = UnivariatePolynomial.parse("x^3", Z);

        // this WILL modify poly1
        p1.add(p2);
        // this will NOT modify poly2
        p2.copy().add(p3);

    }

    @Test
    public void test4() throws Exception {
        UnivariateRing<UnivariatePolynomialZp64> ring = UnivariateRingZp64(17);
        // some random divider
        UnivariatePolynomialZp64 divider = ring.randomElement();
        // some random dividend
        UnivariatePolynomialZp64 dividend = ring.add(
                ring.valueOf(1),
                ring.multiply(divider, ring.valueOf(2)),
                ring.pow(divider, 2));

        // quotient and remainder using built-in methods
        UnivariatePolynomialZp64[] divRemPlain
                = UnivariateDivision.divideAndRemainder(dividend, divider, true);

        // precomputed Newton inverses, need to calculate it only once
        UnivariateDivision.InverseModMonomial<UnivariatePolynomialZp64> invMod
                = UnivariateDivision.fastDivisionPreConditioning(divider);
        // quotient and remainder computed using fast
        // algorithm with precomputed Newton inverses

        UnivariatePolynomialZp64[] divRemFast
                = UnivariateDivision.divideAndRemainderFast(dividend, divider, invMod, true);

        // results are the same
        assert Arrays.equals(divRemPlain, divRemFast);
    }

    @Test
    public void test5() throws Exception {
        // Polynomials over field
        UnivariatePolynomialZp64 a = UnivariatePolynomialZ64.create(1, 3, 2).modulus(17);
        UnivariatePolynomialZp64 b = UnivariatePolynomialZ64.create(1, 0, -1).modulus(17);
        // Euclid and Half-GCD algorithms for polynomials over field
        assert EuclidGCD(a, b).equals(HalfGCD(a, b));
        // Extended Euclidean algorithm
        UnivariatePolynomialZp64[] xgcd = ExtendedEuclidGCD(a, b);
        assert a.copy().multiply(xgcd[1]).add(b.copy().multiply(xgcd[2])).equals(xgcd[0]);
        // Extended Half-GCD algorithm
        UnivariatePolynomialZp64[] xgcd1 = ExtendedHalfGCD(a, b);
        assert Arrays.equals(xgcd, xgcd1);


        // Polynomials over Z
        UnivariatePolynomial<BigInteger> aZ = UnivariatePolynomial.create(1, 3, 2);
        UnivariatePolynomial<BigInteger> bZ = UnivariatePolynomial.create(1, 0, -1);

        // GCD for polynomials over Z
        assert ModularGCD(aZ, bZ).equals(UnivariatePolynomial.create(1, 1));

        // Bivariate polynomials represented as Z[y][x]
        UnivariateRing<UnivariatePolynomial<UnivariatePolynomial<BigInteger>>>
                ringXY = UnivariateRing(UnivariateRing(Z));
        UnivariatePolynomial<UnivariatePolynomial<BigInteger>>
                aXY = ringXY.parse("(1 + y) + (1 + y^2)*x + (y - y^2)*x^2"),
                bXY = ringXY.parse("(3 + y) + (3 + 2*y + y^2)*x + (3*y - y^2)*x^2");
        //    // Subresultant sequence
        PolynomialRemainders<UnivariatePolynomial<UnivariatePolynomial<BigInteger>>>
                subResultants = SubresultantRemainders(aXY, bXY);
        // The GCD
        UnivariatePolynomial<UnivariatePolynomial<BigInteger>> gcdXY = subResultants.gcd().primitivePart();
        assert UnivariateDivision.remainder(aXY, gcdXY, true).isZero();
        assert UnivariateDivision.remainder(bXY, gcdXY, true).isZero();
    }

    @Test
    public void test6() throws Exception {


        // ring GF(13^5)[x] (coefficient domain is finite field)
        UnivariateRing<UnivariatePolynomial<UnivariatePolynomialZp64>> ringF = UnivariateRing(GF(13, 5));
        // some random polynomial composed from some factors
        UnivariatePolynomial<UnivariatePolynomialZp64> polyF = ringF.randomElement().multiply(ringF.randomElement().multiply(polyPow(ringF.randomElement(), 10)));

        // perform square-free factorization
        System.out.println(SquareFreeFactorization(polyF));
        // perform complete factorization
        System.out.println(Factor(polyF));


        // ring Q[x]
        UnivariateRing<UnivariatePolynomial<Rational<BigInteger>>> ringQ = UnivariateRing(Q);
        // some random polynomial composed from some factors
        UnivariatePolynomial<Rational<BigInteger>> polyQ = ringQ.randomElement().multiply(ringQ.randomElement().multiply(polyPow(ringQ.randomElement(), 10)));
        // perform square-free factorization
        System.out.println(SquareFreeFactorization(polyQ));
        // perform complete factorization
        System.out.println(Factor(polyQ));
    }

    @Test
    public void test7() throws Exception {
        Well44497b random = new Well44497b();

        // random irreducible polynomial in Z/2[x] of degree 10
        UnivariatePolynomialZp64 poly1 = randomIrreduciblePolynomial(2, 10, random);
        assert poly1.degree() == 10;
        assert irreducibleQ(poly1);

        // random irreducible polynomial in Z/2[x] of degree 10
        UnivariatePolynomial<BigInteger> poly2 = randomIrreduciblePolynomial(Zp(2), 10, random);
        assert poly2.degree() == 10;
        assert irreducibleQ(poly2);

        // random irreducible polynomial in GF(11^15)[x] of degree 10
        UnivariatePolynomial<UnivariatePolynomialZp64> poly3 = randomIrreduciblePolynomial(GF(11, 15), 10, random);
        assert poly3.degree() == 10;
        assert irreducibleQ(poly3);

        // random irreducible polynomial in Z[x] of degree 10
        UnivariatePolynomial<BigInteger> poly4 = randomIrreduciblePolynomialOverZ(10, random);
        assert poly4.degree() == 10;
        assert irreducibleQ(poly4);
    }

    @Test
    public void test8() throws Exception {
        // points
        long[] points = {1L, 2L, 3L, 12L};
        // values
        long[] values = {3L, 2L, 1L, 6L};

        // interpolate using Newton method
        UnivariatePolynomialZp64 result = new InterpolationZp64(Zp64(17))
                .update(points, values)
                .getInterpolatingPolynomial();

        // result.evaluate(points(i)) = values(i)
        assert IntStream.range(0, points.length).allMatch(i -> result.evaluate(points[i]) == values[i]);
    }


    /**
     * @param <Poly> polynomial type
     */
    static <Poly extends IPolynomial<Poly>> Poly genericFunc(Poly poly) {
        return poly.createOne().add(
                poly.copy().multiply(2),
                polyPow(poly, 2).multiply(3));
    }

    @Test
    public void test9() throws Exception {
        System.out.println(genericFunc(UnivariatePolynomialZ64.create(1, 2, 3).modulus(17)));
        System.out.println(genericFunc(MultivariatePolynomial.parse("1 + x + y + z")));
    }

    /**
     * @param <Poly> polynomial type
     */
    static <Poly extends IPolynomial<Poly>> Poly genericFuncWithRing(Poly poly, Ring<Poly> ring) {
        return ring.add(
                ring.getOne(),
                ring.multiply(poly, ring.valueOf(2)),
                ring.multiply(ring.pow(poly, 2), ring.valueOf(3)));
    }

    @Test
    public void test10() throws Exception {
        UnivariateRing<UnivariatePolynomialZp64> uRing = UnivariateRingZp64(17);
        System.out.println(genericFuncWithRing(uRing.parse("1 + 2*x + 3*x^2"), uRing));

        MultivariateRing<MultivariatePolynomial<BigInteger>> mRing = MultivariateRing(3, Z);
        System.out.println(genericFuncWithRing(mRing.parse("1 + x + y + z"), mRing));
    }

    @Test
    public void test11() throws Exception {
        FiniteField<UnivariatePolynomialZp64> gf = GF(13, 4);
        UnivariatePolynomialZp64 poly = gf.pow(gf.parse("1 + z + z^2 + z^3 + z^4"), 10);

        UnivariatePolynomialZp64 noRing = genericFunc(poly);
        System.out.println(noRing);

        UnivariatePolynomialZp64 withRing = genericFuncWithRing(poly, gf);
        System.out.println(withRing);

        assert !noRing.equals(withRing);
    }


    /**
     * @param <Monomial> type of monomials
     * @param <Poly>     type of multivariate polynomials
     */
    static <Monomial extends DegreeVector<Monomial>,
            Poly extends AMultivariatePolynomial<Monomial, Poly>>
    Poly genericFunc(Poly poly) { return null; }

    /**
     * @param <Monomial> type of monomials
     * @param <Poly>     type of multivariate polynomials
     */
    static <Monomial extends DegreeVector<Monomial>,
            Poly extends AMultivariatePolynomial<Monomial, Poly>>
    Poly genericFuncWithRing(Poly poly, PolynomialRing<Poly> ring) { return null; }

    @Test
    public void test12() throws Exception {
        genericFunc(MultivariatePolynomial.parse("a + b"));

        MultivariateRing<MultivariatePolynomial<BigInteger>> ring = MultivariateRing(3, Z);
        genericFuncWithRing(ring.parse("a + b"), ring);
    }

    @Test
    public void test13() throws Exception {
        MultivariateRing<MultivariatePolynomial<BigInteger>> ring
                = MultivariateRing(2, Z, MonomialOrder.GREVLEX);

        // poly in GREVLEX
        MultivariatePolynomial<BigInteger> poly = ring.parse("x + x^2*y^2 + x*y");
        assert poly.ordering == MonomialOrder.GREVLEX;

        // poly in LEX
        MultivariatePolynomial<BigInteger> poly2 = poly.setOrdering(MonomialOrder.LEX);
        assert poly2.ordering == MonomialOrder.LEX;

        // poly in GREVLEX (ordering of lhs is used)
        MultivariatePolynomial<BigInteger> add = ring.add(poly, poly2);
        assert add.ordering == MonomialOrder.GREVLEX;

        // poly in LEX (ordering of lhs is used)
        MultivariatePolynomial<BigInteger> add2 = ring.add(poly2, poly);
        assert add2.ordering == MonomialOrder.LEX;
    }

    @Test
    public void test14() throws Exception {

        String[] variables = {"x", "y", "z"};
        MultivariatePolynomial<BigInteger>
                dividend = MultivariatePolynomial.parse("x - x^2*y^2 + 2*x*y + 1 - z*y^2*x^2 + z", variables),
                divider1 = MultivariatePolynomial.parse("x + y", variables),
                divider2 = MultivariatePolynomial.parse("x + z", variables),
                divider3 = MultivariatePolynomial.parse("y + z", variables);

        dividend = polyPow(dividend, 3);

        {
            MultivariatePolynomial<BigInteger>[] divRem
                    = MultivariateDivision.divideAndRemainder(dividend, divider1, divider2);

            MultivariatePolynomial<BigInteger>
                    quot1 = divRem[0],
                    quot2 = divRem[1],
                    rem = divRem[2];

            assert dividend.equals(rem.copy().add(
                    quot1.copy().multiply(divider1),
                    quot2.copy().multiply(divider2)));
        }

        {
            MultivariatePolynomial<BigInteger>[] divRem
                    = MultivariateDivision.divideAndRemainder(dividend, divider1, divider2, divider3);

            MultivariatePolynomial<BigInteger>
                    quot1 = divRem[0],
                    quot2 = divRem[1],
                    quot3 = divRem[2],
                    rem = divRem[3];

            assert dividend.equals(rem.copy().add(
                    quot1.copy().multiply(divider1),
                    quot2.copy().multiply(divider2),
                    quot3.copy().multiply(divider3)));
        }
    }

    @Test
    public void test15() throws Exception {


        // some large finite field
        IntegersZp64 zpRing = Zp64(SmallPrimes.nextPrime(1 << 15));
        MultivariatePolynomialZp64
                a = MultivariatePolynomialZp64.parse("x^2 - x*y + z^5", zpRing),
                b = MultivariatePolynomialZp64.parse("x^2 + x*y^7 + x*y*z^2", zpRing);

        MultivariatePolynomialZp64
                gcd = MultivariatePolynomialZp64.parse("x + y + z", zpRing),
                poly1 = a.copy().multiply(gcd),
                poly2 = b.copy().multiply(gcd);

        // EZGCD in finite field
        MultivariatePolynomialZp64 ez = EZGCD(poly1, poly2);
        assert ez.equals(gcd);

        // EEZGCD in finite field
        MultivariatePolynomialZp64 eez = EEZGCD(poly1, poly2);
        assert eez.equals(gcd);

        // ZippelGCD in finite field
        MultivariatePolynomialZp64 zippel = ZippelGCD(poly1, poly2);
        assert zippel.equals(gcd);

        // some very small finite field (Z/2)
        IntegersZp64 z2 = Zp64(2);
        MultivariatePolynomialZp64
                z2GCD = gcd.setRing(z2),
                z2Poly1 = a.setRing(z2).multiply(z2GCD),
                z2Poly2 = b.setRing(z2).multiply(z2GCD);

        // Kaltofen’s & Monagan’s generic modular GCD
        MultivariatePolynomialZp64 modGF = MultivariateGCD.KaltofenMonaganSparseModularGCDInGF(z2Poly1, z2Poly2);
        assert modGF.equals(z2GCD);

        // Z
        MultivariatePolynomial<BigInteger>
                zGCD = gcd.setRing(Z),
                zPoly1 = a.setRing(Z).multiply(zGCD),
                zPoly2 = b.setRing(Z).multiply(zGCD);

        // Modular GCD in Z with sparse interpolation
        MultivariatePolynomial<BigInteger> mod = ZippelGCDInZ(zPoly1, zPoly2);
        assert mod.equals(zGCD);
    }

    @Test
    @SuppressWarnings("unchecked")
    public void test16() throws Exception {
        MultivariateRing<MultivariatePolynomial<BigInteger>> ring = MultivariateRing(3, Z);
        int rndDegree = 5, rndSize = 5;

        // some random gcd
        MultivariatePolynomial<BigInteger> gcd = ring.randomElement(rndDegree, rndSize);
        // array of random polynomials which have gcd
        MultivariatePolynomial<BigInteger>[] polys = IntStream.range(0, 10)
                .mapToObj(i -> ring.randomElement(rndDegree, rndSize).multiply(gcd))
                .toArray(MultivariatePolynomial[]::new);

        // fast algorithm for array of polynomials will be used
        MultivariatePolynomial<BigInteger> fastGCD = MultivariateGCD.PolynomialGCD(polys);
        // slow step-by-step gcd calculation
        MultivariatePolynomial<BigInteger> slowGCD = Arrays.stream(polys)
                .reduce(ring.getZero(), MultivariateGCD::PolynomialGCD);
        // result the same
        assert fastGCD.equals(slowGCD) || fastGCD.equals(slowGCD.negate());
    }

    @Test
    public void test17() throws Exception {
        // ring GF(13^5)[x, y, z] (coefficient domain is finite field)
        MultivariateRing<MultivariatePolynomial<UnivariatePolynomialZp64>>
                ringF = MultivariateRing(3, GF(13, 5));

        // generate random poly of degree 5 and size 5
        Supplier<MultivariatePolynomial<UnivariatePolynomialZp64>> randomPolyF
                = () -> ringF.randomElement(5, 5).increment();

        // some random polynomial composed from some factors
        MultivariatePolynomial<UnivariatePolynomialZp64> polyF =
                randomPolyF.get().multiply(
                        randomPolyF.get(), ringF.pow(randomPolyF.get(), 2));
        // perform square-free factorization
        System.out.println(FactorSquareFree(polyF));
        // perform complete factorization
        System.out.println(Factor(polyF));


        // ring Q[x, y, z]
        MultivariateRing<MultivariatePolynomial<Rational<BigInteger>>> ringQ = MultivariateRing(3, Q);

        Supplier<MultivariatePolynomial<Rational<BigInteger>>> randomPolyQ
                = () -> ringQ.randomElement(5, 5).increment();
        // some random polynomial composed from some factors
        MultivariatePolynomial<Rational<BigInteger>> polyQ =
                randomPolyQ.get().multiply(
                        randomPolyQ.get(), ringQ.pow(randomPolyQ.get(), 2));
        // perform square-free factorization
        System.out.println(FactorSquareFree(polyQ));
        // perform complete factorization
        System.out.println(Factor(polyQ));
    }

    @Test
    public void test18() throws Exception {

        // ring GF(13^6)[x, y, z]
        FiniteField<UnivariatePolynomialZp64> cfRing = GF(13, 6);
        MultivariateRing<MultivariatePolynomial<UnivariatePolynomialZp64>> ring = MultivariateRing(3, cfRing);


        UnivariatePolynomialZp64[] points = {
                cfRing.parse("1 + t"),
                cfRing.parse("2 + t"),
                cfRing.parse("3 + t"),
                cfRing.parse("12 + t")
        };

        String[] vars = {"x", "y", "z"};
        // some values for interpolation
        MultivariatePolynomial[] values = {
                ring.parse("x + y", vars),
                ring.parse(" x^2 + (t) * y", vars),
                ring.parse("y^3", vars),
                ring.parse("(t) * x^4 + y", vars)
        };

        // interpolation polynomial values for variable z
        MultivariatePolynomial<UnivariatePolynomialZp64> result =
                new MultivariateInterpolation.Interpolation(2, ring)
                        .update(points, values)
                        .getInterpolatingPolynomial();

        assert IntStream.range(0, points.length).allMatch(i -> result.evaluate(2, points[i]).equals(values[i]));
    }

    @Test
    public void test19() throws Exception {

        // Galois field GF(7^10)
        // (irreducible polynomial will be generated automatically)
        FiniteField<UnivariatePolynomialZp64> gf7_10 = GF(7, 10);
        assert gf7_10.characteristic().intValue() == 7;
        assert gf7_10.cardinality().equals(BigInteger.valueOf(7).pow(10));

        // GF(7^3) generated by irreducible polynomial "1 + 3*z + z^2 + z^3"
        FiniteField<UnivariatePolynomialZp64> gf7_3 = GF(UnivariatePolynomialZ64.create(1, 3, 1, 1).modulus(7));
        assert gf7_3.characteristic().intValue() == 7;
        assert gf7_3.cardinality().intValue() == 7 * 7 * 7;
    }

    @Test
    public void test20() throws Exception {
        // ring Z
        Ring<BigInteger> notField = Z;
        // it is not a fielf
        assert !notField.isField();
        // this is OK
        assert 1 == notField.reciprocal(Z.valueOf(1)).intValue();
        // this will throw ArithmeticException
        notField.reciprocal(Z.valueOf(10));
    }

    @Test
    public void test21() throws Exception {
        int intNumber = 1234567;
        // false
        boolean primeQ = SmallPrimes.isPrime(intNumber);
        // 1234577
        int intPrime = SmallPrimes.nextPrime(intNumber);
        // [127, 9721]
        int[] intFactors = SmallPrimes.primeFactors(intNumber);

        long longNumber = 12345671234567123L;
        // false
        primeQ = BigPrimes.isPrime(longNumber);
        // 12345671234567149
        long longPrime = BigPrimes.nextPrime(longNumber);
        // [1323599, 9327350077]
        long[] longFactors = BigPrimes.primeFactors(longNumber);

        BigInteger bigNumber = Z.parse("321536584276145124691487234561832756183746531874567");
        // false
        primeQ = BigPrimes.isPrime(bigNumber);
        // 321536584276145124691487234561832756183746531874827
        BigInteger bigPrime = BigPrimes.nextPrime(bigNumber);
        // [3, 29, 191, 797359, 1579057, 14916359, 1030298906727233717673336103]
        List<BigInteger> bigFactors = BigPrimes.primeFactors(bigNumber);
    }

    @Test
    public void test22() throws Exception {
        Rationals<BigInteger> field = Frac(Z);     // the same as Q

        Rational<BigInteger>
                a = field.parse("13/6"),
                b = field.parse("2/3"),
                c = field.parse("3/2");

        assert field.parse("13/6")
                .equals(field.add(
                        field.parse("2/3"),
                        field.parse("3/2")));

        assert field.parse("5/6")
                .equals(field.add(
                        field.parse("2/3"),
                        field.parse("1/6")));

    }

    @Test
    public void test23() throws Exception {
        // Ring Z/3[x]
        UnivariateRing<UnivariatePolynomialZp64> zp3x = UnivariateRingZp64(3);
        // parse univariate poly from string
        UnivariatePolynomialZp64
                p1 = zp3x.parse("4 + 8*x + 13*x^2"),
                p2 = zp3x.parse("4 - 8*x + 13*x^2");
        assert zp3x.add(p1, p2).equals(zp3x.parse("2 - x^2"));


        // GF(7^3)
        FiniteField<UnivariatePolynomialZp64> cfRing = GF(UnivariateRingZp64(7).parse("1 + 3*z + z^2 + z^3"));
        // GF(7^3)[x]
        UnivariateRing<UnivariatePolynomial<UnivariatePolynomialZp64>> gfx = UnivariateRing(cfRing);
        // parse univariate poly from string
        UnivariatePolynomial<UnivariatePolynomialZp64>
                r1 = gfx.parse("4 + (8 + z)*x + (13 - z^43)*x^2"),
                r2 = gfx.parse("4 - (8 + z)*x + (13 + z^43)*x^2");
        assert gfx.add(r1, r2).equals(gfx.parse("1 - 2*x^2"));
        UnivariatePolynomial<UnivariatePolynomialZp64>
                divRem[] = divideAndRemainder(r1, r2),
                div = divRem[0],
                rem = divRem[1];
        assert r1.equals(gfx.add(gfx.multiply(r2, div), rem));
    }

    @Test
    public void test24() throws Exception {
        String[] vars = {"x", "y", "z"};
        // Ring Z/3[x, y, z]
        MultivariateRing<MultivariatePolynomialZp64> zp3xyz = MultivariateRingZp64(3, 3);
        // parse univariate poly from string
        MultivariatePolynomialZp64
                p1 = zp3xyz.parse("4 + 8*x*y + 13*x^2*z^5", vars),
                p2 = zp3xyz.parse("4 - 8*x*y + 13*x^2*z^5", vars);
        assert zp3xyz.add(p1, p2).equals(zp3xyz.parse("2 - x^2*z^5", vars));


        // GF(7^3)
        FiniteField<UnivariatePolynomialZp64> cfRing = GF(UnivariateRingZp64(7).parse("1 + 3*z + z^2 + z^3"));
        // GF(7^3)[x]
        MultivariateRing<MultivariatePolynomial<UnivariatePolynomialZp64>> gfxyz = MultivariateRing(3, cfRing);
        // parse univariate poly from string
        MultivariatePolynomial<UnivariatePolynomialZp64>
                r1 = gfxyz.parse("4 + (8 + z)*x*y + (13 - z^43)*x^2*z^5", vars),
                r2 = gfxyz.parse("4 - (8 + z)*x*y + (13 + z^43)*x^2*z^5", vars);
        assert gfxyz.add(r1, r2).equals(gfxyz.parse("1 - 2*x^2*z^5", vars));
        MultivariatePolynomial<UnivariatePolynomialZp64>
                divRem[] = divideAndRemainder(r1, r2),
                div = divRem[0],
                rem = divRem[1];
        assert r1.equals(gfxyz.add(gfxyz.multiply(r2, div), rem));
    }

    @Test
    public void test25() throws Exception {
        FiniteField<UnivariatePolynomialZp64> ring = GF(17, 9);

        UnivariatePolynomialZp64 a = ring.randomElement();
        UnivariatePolynomialZp64 b = ring.pow(a, 1000);
        UnivariatePolynomialZp64 c = ring.reciprocal(b);

        assert ring.multiply(b, c).isOne();

        UnivariatePolynomialZp64 some = ring.add(
                ring.divideExact(a, ring.add(b, c)),
                ring.pow(a, 6),
                ring.negate(ring.multiply(a, b, c)));
    }

    @Test
    public void test26() throws Exception {
        // Z[x, y, z]
        MultivariateRing<MultivariatePolynomial<BigInteger>> ring = MultivariateRing(3, Z, MonomialOrder.LEX);

        MultivariatePolynomial<BigInteger>
                x = ring.variable(0),
                y = ring.variable(1),
                z = ring.variable(2);

        // do some math
        MultivariatePolynomial<BigInteger> a = ring.decrement(ring.pow(ring.add(x, y, z), 2));
        MultivariatePolynomial<BigInteger> b = ring.add(
                ring.pow(ring.add(x, ring.negate(y), ring.negate(z), ring.getNegativeOne()), 2),
                x, y, z, ring.getNegativeOne());
        MultivariatePolynomial<BigInteger> c = ring.add(
                ring.pow(ring.add(a, b, ring.getOne()), 9),
                ring.negate(a), ring.negate(b), ring.getNegativeOne());

        // reduce c modulo a and b (multivariate division with remainder)
        MultivariatePolynomial<BigInteger>[] divRem = MultivariateDivision.divideAndRemainder(c, a, b);
        MultivariatePolynomial<BigInteger>
                div1 = divRem[0],
                div2 = divRem[1],
                rem = divRem[2];

    }
}