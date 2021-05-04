package cc.redberry.rings.poly.univar;

import cc.redberry.rings.IntegersZp;
import cc.redberry.rings.IntegersZp64;
import cc.redberry.rings.Rings;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.io.Coder;
import cc.redberry.rings.poly.FiniteField;
import cc.redberry.rings.poly.MultivariateRing;
import cc.redberry.rings.poly.multivar.MonomialOrder;
import cc.redberry.rings.poly.multivar.MultivariatePolynomialZp64;
import cc.redberry.rings.test.Benchmark;
import cc.redberry.rings.util.RandomDataGenerator;
import cc.redberry.rings.util.TimeUnits;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well512a;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.Assert;
import org.junit.Test;

import static cc.redberry.rings.poly.univar.RandomUnivariatePolynomials.randomPoly;
import static cc.redberry.rings.poly.univar.UnivariatePolynomial.MUL_CLASSICAL_THRESHOLD;

/**
 * @since 1.0
 */
public class UnivariatePolynomialTest extends AUnivariateTest {

    @Test
    public void test1() throws Exception {
        BigInteger modulus = BigInteger.valueOf(59);
        UnivariatePolynomial<BigInteger> aZ = UnivariatePolynomial.create(Rings.Z, 1, 2, 3, 4, 5, 6);
        IntegersZp domain = new IntegersZp(modulus);
        UnivariatePolynomial<BigInteger> aZp = aZ.setRing(domain);
        UnivariatePolynomialZp64 aL = UnivariatePolynomial.asOverZp64(aZp);

        for (int i = 0; i < 5; i++) {
//            a = (a.clone() * a.clone().decrement() - a.clone().derivative() + (a.clone().square())) * a.clone();
            aZp = (aZp.clone().multiply(aZp.clone().decrement()).subtract(aZp.clone().derivative()).add(aZp.clone().square())).multiply(aZp.clone());
            aZp = aZp.truncate(aZp.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            aZp = aZp.subtract(aZp.derivative()).decrement();
//            a = a.multiply(a.derivative().increment().truncate(10));

            aZ = (aZ.clone().multiply(aZ.clone().decrement()).subtract(aZ.clone().derivative()).add(aZ.clone().square())).multiply(aZ.clone());
            aZ = aZ.truncate(aZ.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            aZ = aZ.subtract(aZ.derivative()).decrement();
//            aZ = aZ.multiply(aZ.derivative().increment().truncate(10));

            aL = (aL.clone().multiply(aL.clone().decrement()).subtract(aL.clone().derivative()).add(aL.clone().square())).multiply(aL.clone());
            aL = aL.truncate(aL.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            aL = aL.subtract(aL.derivative()).decrement();
//            aL = aL.multiply(aL.derivative().increment().truncate(10));
        }

        System.out.println(aZp.degree);
        Assert.assertEquals(aL, UnivariatePolynomial.asOverZp64(aZp));
        Assert.assertEquals(aZp, aZ.setRing(domain));
    }

    @Test
    public void test3() throws Exception {
        Assert.assertEquals(-1, UnivariatePolynomial.create(0).firstNonZeroCoefficientPosition());
        Assert.assertEquals(-1, UnivariatePolynomial.create(0, 0, 0).firstNonZeroCoefficientPosition());
        Assert.assertEquals(0, UnivariatePolynomial.create(1).firstNonZeroCoefficientPosition());
        Assert.assertEquals(1, UnivariatePolynomial.create(0, 1).firstNonZeroCoefficientPosition());
    }

    @Test
    public void test4() throws Exception {
        UnivariatePolynomial<UnivariatePolynomialZp64> poly = UnivariatePolynomial.create(FiniteField.GF17p5, UnivariatePolynomialZ64.zero().modulus(17));
        Assert.assertEquals("0", poly.toString());
    }

    @Test
    public void test5() throws Exception {
        IntegersZp64 lDomain = new IntegersZp64(11);
        MultivariateRing<MultivariatePolynomialZp64> domain = new MultivariateRing<>(MultivariatePolynomialZp64.zero(4, lDomain, MonomialOrder.LEX));
        Coder<MultivariatePolynomialZp64, ?, ?> mParser = Coder.mkPolynomialCoder(domain, "x1", "x2", "x3", "x4");
        Coder<UnivariatePolynomial<MultivariatePolynomialZp64>, ?, ?> parser = Coder.mkUnivariateCoder(Rings.UnivariateRing(domain), mParser, "x");
        UnivariatePolynomial<MultivariatePolynomialZp64> poly = parser.parse("(6*x3)+(10*x2*x3^2*x4^2)*x^3");
        for (int i = 0; i < 1000; i++)
            Assert.assertFalse(poly.content().isZero());
    }

    @Test
    public void test6() {
        Assert.assertEquals(
                UnivariatePolynomial.create(1, 2 * 2, 2 * 2 * 3, 2 * 2 * 2 * 4, 2 * 2 * 2 * 2 * 5),
                UnivariatePolynomial.create(1, 2, 3, 4, 5).scale(BigInteger.valueOf(2)));
    }

    @Test
    public void testKronecker1() {
        DescriptiveStatistics stat = testKroneckerRandom(2, 150, 35, false, its(1000, 5000), new Well512a());
        System.out.println(stat);
    }

    @Test
    @Benchmark
    public void testKronecker2() {
        DescriptiveStatistics stat = testKroneckerRandom(1000, 3000,
                135, true, 100, new Well512a());
        System.out.println(stat);
    }

    @Test
    @Benchmark
    public void testKronecker3_deg_dep() {
        Well512a rnd = new Well512a();
        //warm up
        testKroneckerRandom(100, 1000, 135, false, 100, rnd);

        for (int degree = 10; degree < 100; degree += 5) {
            DescriptiveStatistics stat = testKroneckerRandom((int) (degree * 0.9), (int) (degree * 1.1),
                    135, false, 500, rnd);
            System.out.println(degree + " : " + stat.getPercentile(50));
        }

        for (int degree = 10; degree < 1000; degree += 50) {
            DescriptiveStatistics stat = testKroneckerRandom((int) (degree * 0.9), (int) (degree * 1.1),
                    135, false, 100, rnd);
            System.out.println(degree + " : " + stat.getPercentile(50));
        }
    }

    @Test
    @Benchmark
    public void testKronecker4_bound_dep() {
        Well512a rnd = new Well512a();
        //warm up
        testKroneckerRandom(100, 1000, 135, false, 100, rnd);

        for (int boundBitLen = 10; boundBitLen < 1000; boundBitLen += 50) {
            DescriptiveStatistics stat = testKroneckerRandom(450, 550,
                    boundBitLen, false, 500, rnd);
            System.out.println(boundBitLen + " : " + stat.getMean());
        }
    }

    @Test
    @Benchmark
    public void testKronecker5_skewness() {
        Well512a rnd = new Well512a();
        //warm up
        testKroneckerRandom(100, 1000, 135, false, 500, rnd);
        System.out.println("warm up done");

        for (int aDeg = 50; aDeg <= 1000; aDeg += 50)
            for (int bDeg = 50; bDeg <= 3000; bDeg += 50) {
                DescriptiveStatistics stat = testKroneckerRandom(
                        (int) (aDeg * 0.9), (int) (aDeg * 1.1),
                        (int) (bDeg * 0.9), (int) (bDeg * 1.1),
                        135, false, 100, rnd);
                System.out.println(aDeg + " - " + bDeg + " : " + stat.getPercentile(50));
            }
    }

    @Test
    @Benchmark
    public void testKronecker6_skewness() {
        Well512a rnd = new Well512a();
        //warm up
        testKroneckerRandom(100, 1000, 135, false, 500, rnd);
        System.out.println("warm up done");

        System.out.println(testKroneckerRandom(
                200, 250,
                5000, 5500,
                135, false, 2, rnd).getPercentile(50));
    }

    /* For usage in tests */
    static <E> UnivariatePolynomial<E> multiplyKaratsuba(UnivariatePolynomial<E> p, UnivariatePolynomial<E> oth) {
        E[] res;
        if (1L * (p.degree + 1) * (p.degree + 1) <= MUL_CLASSICAL_THRESHOLD)
            res = p.multiplyClassicalSafe(p.data, 0, p.degree + 1, oth.data, 0, oth.degree + 1);
        else
            res = p.multiplyKaratsubaSafe(p.data, 0, p.degree + 1, oth.data, 0, oth.degree + 1);

        return p.createFromArray(res);
    }

    public static DescriptiveStatistics testKroneckerRandom(int minDeg, int maxDeg, int boundBitLen,
                                                            boolean sout, int its, RandomGenerator rnd) {
        return testKroneckerRandom(minDeg, maxDeg, minDeg, maxDeg, boundBitLen, sout, its, rnd);
    }

    public static DescriptiveStatistics testKroneckerRandom(int aMinDeg, int aMaxDeg,
                                                            int bMinDeg, int bMaxDeg,
                                                            int boundBitLen,
                                                            boolean sout, int its, RandomGenerator rnd) {
        RandomDataGenerator rng = new RandomDataGenerator(rnd);
        BigInteger cfBound = BigInteger.ONE.shiftLeft(boundBitLen);

        DescriptiveStatistics stat = new DescriptiveStatistics();
        for (int i = 0; i < its; i++) {
            long st;

            UnivariatePolynomial<BigInteger> a = randomPoly(rng.nextInt(aMinDeg, aMaxDeg), cfBound, rnd);
            UnivariatePolynomial<BigInteger> b = randomPoly(rng.nextInt(bMinDeg, bMaxDeg), cfBound, rnd);

            st = System.nanoTime();
            UnivariatePolynomial<BigInteger> kro = UnivariatePolynomial.multiplyKronecker(a, b);
            long kroTime = System.nanoTime() - st;
            if (sout)
                System.out.println("Kronecker: " + TimeUnits.nanosecondsToString(kroTime));


            st = System.nanoTime();
            Object kar = multiplyKaratsuba(a, b);
            long karTim = System.nanoTime() - st;
            if (sout) {
                System.out.println("Karatsuba: " + TimeUnits.nanosecondsToString(karTim));
                System.out.println();
            }

            stat.addValue(1.0 * kroTime / karTim);
            Assert.assertEquals(kro, kar);
        }

        return stat;
    }

    @Test
    @Benchmark
    public void testUnoptimizedKronecker1() {
        UnivariatePolynomial<BigInteger> a = UnivariatePolynomial.create(1, 2, 1);
        UnivariatePolynomial<BigInteger> b = UnivariatePolynomial.create(1, 1, 1, 2, 1, 1, 1, 3, 1, 1);
        a = a.shiftRight(111814).increment();
        b = b.shiftRight(111001).increment();

        for (int i = 0; i < 1000; i++) {
            long time;

            time = System.nanoTime();
            UnivariatePolynomial<BigInteger> opt = UnivariatePolynomial.multiplyKronecker(a, b);
            System.out.println("Optimized Kronecker: " + TimeUnits.nanosecondsToString(System.nanoTime() - time));

            time = System.nanoTime();
            Object nOpt = unoptimizedKronecker(a, b);
            System.out.println("Not optimized Kronecker " + TimeUnits.nanosecondsToString(System.nanoTime() - time));

            time = System.nanoTime();
            Object kar = multiplyKaratsuba(a, b);
            System.out.println("Karatsuba: " + TimeUnits.nanosecondsToString(System.nanoTime() - time));

            Assert.assertEquals(opt, kar);
            Assert.assertEquals(opt, nOpt);

            System.out.println();
        }
    }

    /** Fast polynomial evaluation at power of two */
    private static BigInteger evalAtPowerOf2(UnivariatePolynomial<BigInteger> a, int bitLen) {
        BigInteger res = a.cc();
        for (int i = 1; i <= a.degree; ++i)
            res = res.add(a.get(i).shiftLeft(i * bitLen));
        return res;
    }

    /**
     * Univariate multiplication with Kronecker substitution using Schoenhage-Strassen multiplication for integers; only
     * for polynomials with positive coefficients
     */
    private static UnivariatePolynomial<BigInteger>
    unoptimizedKronecker(UnivariatePolynomial<BigInteger> a,
                         UnivariatePolynomial<BigInteger> b) {
        // coefficient bound
        BigInteger cfBound =
                a.maxAbsCoefficient()
                        .multiply(b.maxAbsCoefficient())
                        .multiply(BigInteger.valueOf(Math.min(a.degree, b.degree)));
        // point for Kronecker substitution (power of two) is 2^bitLen
        int bitLen = cfBound.bitLength() + 1;

        // evaluate fast of a and b at point
        BigInteger
                aVal = evalAtPowerOf2(a, bitLen),
                bVal = evalAtPowerOf2(b, bitLen);

        // packed result, Schoenhage-Strassen is used internally for multiplication
        // when aVal & bVal bit length > 8720
        BigInteger packedResult = aVal.multiply(bVal);
        // unpacked result
        BigInteger[] unpackedResult = new BigInteger[a.degree + b.degree + 1];
        // unpacking
        for (int i = a.degree + b.degree; i > 0; --i) {
            BigInteger
                    div = packedResult.shiftRight(i * bitLen),
                    rem = packedResult.subtract(div.shiftLeft(i * bitLen));

            unpackedResult[i] = div;
            packedResult = rem;
        }
        unpackedResult[0] = packedResult;
        return UnivariatePolynomial.create(a.ring, unpackedResult);
    }
}
