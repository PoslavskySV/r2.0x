package cc.redberry.rings.poly.univar;

import cc.redberry.rings.IntegersZp;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.PolynomialFactorDecomposition;
import cc.redberry.rings.poly.FiniteField;
import cc.redberry.rings.poly.univar.FactorizationTestUtil.RandomSource;
import cc.redberry.rings.test.Benchmark;
import cc.redberry.rings.util.RandomUtil;
import org.apache.commons.math3.random.RandomDataGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.Test;

import static cc.redberry.rings.poly.FactorDecompositionTest.assertFactorization;
import static cc.redberry.rings.poly.univar.UnivariateSquareFreeFactorization.SquareFreeFactorization;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by poslavsky on 20/01/2017.
 */
public class UnivariateSquareFreeFactorizationTest extends AUnivariateTest {
    @Test
    public void test1() throws Exception {
        UnivariatePolynomialZ64 poly = UnivariatePolynomialArithmetic.polyPow(UnivariatePolynomialZ64.create(1, 3).multiply(2), 3, false).multiply(UnivariatePolynomialArithmetic.polyPow(UnivariatePolynomialZ64.create(-3, -5, 7), 2, false));
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly));
        poly = UnivariatePolynomialZ64.create(1, 3);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly));
        poly = UnivariatePolynomialZ64.create(3);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly));
        poly = UnivariatePolynomialZ64.create(33);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly));
        poly = UnivariatePolynomialZ64.create(22, 22).multiply(UnivariatePolynomialZ64.create(12, 12, 12)).multiply(12);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly));
    }

    @Test
    @Benchmark(runAnyway = true)
    public void testRandom2() throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = new RandomDataGenerator(rnd);
        DescriptiveStatistics yun = new DescriptiveStatistics(), musser = new DescriptiveStatistics();

        long overflows = 0;
        for (int i = 0; i < its(1000, 5000); i++) {
            if (i == 100) {
                yun.clear();
                musser.clear();
            }
            int nbase = rndd.nextInt(1, 5);
            UnivariatePolynomialZ64 poly;
            try {
                poly = UnivariatePolynomialZ64.create(rndd.nextLong(1, 10));
                for (int j = 0; j < nbase; j++) {
                    UnivariatePolynomialZ64 factor = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(1, 3), 10, rnd);
                    int exponent = rndd.nextInt(1, 5);
                    poly = poly.multiply(UnivariatePolynomialArithmetic.polyPow(factor, exponent, true));
                }
            } catch (ArithmeticException e) {
                --i;
                continue;
            }
            try {
                long start = System.nanoTime();
                PolynomialFactorDecomposition<UnivariatePolynomialZ64> yunFactorization = UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly);
                yun.addValue(System.nanoTime() - start);

                start = System.nanoTime();
                PolynomialFactorDecomposition<UnivariatePolynomialZ64> musserFactorization = UnivariateSquareFreeFactorization.SquareFreeFactorizationMusserZeroCharacteristics(poly);
                musser.addValue(System.nanoTime() - start);

                assertEquals(yunFactorization.factors.size(), musserFactorization.factors.size());
                assertFactorization(poly, musserFactorization);
                assertFactorization(poly, yunFactorization);
            } catch (ArithmeticException exc) {
                if (!exc.getMessage().contains("overflow"))
                    throw exc;
                ++overflows;
            }
        }

        System.out.println("Overflows: " + overflows);
        System.out.println("Timings    Yun: " + yun.getMean());
        System.out.println("Timings Musser: " + musser.getMean());
    }

    @Test
    public void test3() throws Exception {
        UnivariatePolynomialZ64 poly = UnivariatePolynomialZ64.create(0, 0, -1458, 6561, -6561);
        PolynomialFactorDecomposition<UnivariatePolynomialZ64> factorization = UnivariateSquareFreeFactorization.SquareFreeFactorizationYun0(poly);
        assertFactorization(poly, factorization);
    }


    @Test
    public void test4() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(1, 0, 1, 0, 2).modulus(2);
        poly = poly.multiply(UnivariatePolynomialZ64.create(1, 0, 1, 0, 2).modulus(2));
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test5() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(1, 0, 0, 0, 1).modulus(2);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    @Benchmark(runAnyway = true)
    public void testRandom6() throws Exception {
        final class test {
            long overflows = 0;
            final DescriptiveStatistics arithmetics = new DescriptiveStatistics();
            final DescriptiveStatistics timings = new DescriptiveStatistics();

            void run(int bound, int maxDegree, int maxNBase, int maxExponent, int nIterations) {
                RandomGenerator rnd = getRandom();
                RandomDataGenerator rndd = new RandomDataGenerator(rnd);
                long start;
                for (int i = 0; i < nIterations; i++) {
                    if (i == 100)
                        timings.clear();
                    int nbase = rndd.nextInt(1, maxNBase);
                    for (long modulus : getModulusArray(9, 1, 35)) {
                        UnivariatePolynomialZp64 poly;
                        start = System.nanoTime();
                        poly = UnivariatePolynomialZ64.create(rndd.nextLong(1, 1000)).modulus(modulus, false);
                        for (int j = 0; j < nbase; j++) {
                            UnivariatePolynomialZp64 f = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(1, maxDegree), bound, rnd).modulus(modulus);
                            poly = poly.multiply(UnivariatePolynomialArithmetic.polyPow(f, rndd.nextInt(1, maxExponent), true));
                        }
                        arithmetics.addValue(System.nanoTime() - start);
                        try {
                            start = System.nanoTime();
                            PolynomialFactorDecomposition<UnivariatePolynomialZp64> factorization = UnivariateSquareFreeFactorization.SquareFreeFactorization(poly);
                            timings.addValue(System.nanoTime() - start);
                            assertFactorization(poly, factorization);
                        } catch (ArithmeticException exc) {
                            if (!exc.getMessage().contains("overflow"))
                                throw exc;
                            ++overflows;
                        }

                    }
                }
            }
        }
        test smallPolys = new test();
        smallPolys.run(10, 3, 5, 5, (int) its(100, 1000));
        System.out.println("Overflows: " + smallPolys.overflows);
        System.out.println("Timings:\n" + smallPolys.timings.getPercentile(50));
        System.out.println("Arithmetics:\n" + smallPolys.arithmetics.getPercentile(50));

        System.out.println("\n================== \n");
        test largePolys = new test();
        largePolys.run(1000, 15, 10, 20, (int) its(10, 10));
        System.out.println("Overflows: " + largePolys.overflows);
        System.out.println("Timings:\n" + largePolys.timings.getPercentile(50));
        System.out.println("Arithmetics:\n" + largePolys.arithmetics.getPercentile(50));
    }

    @Test
    public void test6a() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(0, 0, 1, 3, 4, 3, 3, 2, 3).modulus(5);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6b() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(0, 0, 0, 2).modulus(3);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6c() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(0, 0, 0, 1, 1).modulus(2);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6d() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2).modulus(3);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6e() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(2, 3, 2, 1, 3, 3, 3).modulus(5);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6f() throws Exception {
        UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1).modulus(3);
        assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
    }

    @Test
    public void test6g() throws Exception {
        for (long modulus : getModulusArray(1, 1, 50)) {
            UnivariatePolynomialZp64 poly = UnivariatePolynomialZ64.create(0, 0, 0, 8, 20, 67, 55).modulus(modulus);
            assertFactorization(poly, UnivariateSquareFreeFactorization.SquareFreeFactorization(poly));
        }
    }

    @Test
    public void test7() throws Exception {
        assertEquals(1, UnivariateSquareFreeFactorization.SquareFreeFactorization(UnivariatePolynomialZ64.create(0, 0, 0, 0, 1)).factors.size());
        assertEquals(1, UnivariateSquareFreeFactorization.SquareFreeFactorization(UnivariatePolynomialZ64.create(0, 0, 0, 0, 1).modulus(31)).factors.size());
    }

    @Test
    public void test8() throws Exception {
        RandomSource rnd = new RandomSource(getRandom(), 10, 20, false);
        long modulus = 3;
        for (int i = 0; i < 1000; i++) {
            UnivariatePolynomialZp64 poly = rnd.take(modulus);
            assertTrue(UnivariateSquareFreeFactorization.isSquareFree(UnivariateSquareFreeFactorization.SquareFreePart(poly)));
        }
    }

    @Test
    public void test9() throws Exception {
        assertTrue(UnivariateSquareFreeFactorization.SquareFreeFactorization(UnivariatePolynomialZ64.create(3, 7).modulus(17)).get(0).isMonic());
    }

    @Test
    public void test10() throws Exception {
        UnivariatePolynomial<BigInteger> poly = UnivariatePolynomial.create(Long.MAX_VALUE, Long.MAX_VALUE - 1, Long.MAX_VALUE - 2, Long.MAX_VALUE - 3);
        UnivariatePolynomial<BigInteger> original = poly.add(poly.derivative());
        UnivariatePolynomial<BigInteger> squared = original.clone().square();

        PolynomialFactorDecomposition<UnivariatePolynomial<BigInteger>> f = SquareFreeFactorization(squared);
        assertEquals(1, f.size());
        assertEquals(2, f.getExponent(0));
        assertEquals(original, f.get(0));

        UnivariatePolynomial<BigInteger> squaredMod = squared.setRing(new IntegersZp(BigInteger.LONG_MAX_VALUE.multiply(BigInteger.TWO).nextProbablePrime()));
        squaredMod = squaredMod.square();

        PolynomialFactorDecomposition<UnivariatePolynomial<BigInteger>> fMod = SquareFreeFactorization(squaredMod);
        assertEquals(1, fMod.size());
        assertEquals(4, fMod.getExponent(0));
        assertFactorization(squaredMod, fMod);
    }

    @Test
    public void testRandom11() throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = new RandomDataGenerator(rnd);
        BigInteger bound = BigInteger.LONG_MAX_VALUE;
        bound = bound.multiply(bound).increment();
        int nIterations = (int) its(20, 50);
        for (int i = 0; i < nIterations; i++) {
            UnivariatePolynomial<BigInteger> poly;
            poly = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(2, 30), bound, rnd);
            int exponent = rndd.nextInt(2, 4);
            poly = UnivariatePolynomialArithmetic.polyPow(poly, exponent, false);

            PolynomialFactorDecomposition<UnivariatePolynomial<BigInteger>> zf = SquareFreeFactorization(poly);
            assertTrue(zf.sumExponents() >= exponent);
            assertFactorization(poly, zf);

            UnivariatePolynomial<BigInteger> polyMod = poly.setRing(new IntegersZp(RandomUtil.randomInt(bound, rnd).nextProbablePrime()));
            PolynomialFactorDecomposition<UnivariatePolynomial<BigInteger>> zpf = SquareFreeFactorization(polyMod);
            assertTrue(zpf.sumExponents() >= exponent);
            assertFactorization(polyMod, zpf);
        }
    }

    @Test
    public void test11() throws Exception {
        UnivariatePolynomialZp64
                a = UnivariatePolynomialZ64.create(1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 6).modulus(7),
                b = UnivariatePolynomialZ64.create(1, 2, 3, 4, 5, 6, 5, 4).modulus(7),
                poly = a.square().multiply(b.square());
        assertFactorization(poly, SquareFreeFactorization(poly));
    }

    @Test
    public void testFiniteField1() throws Exception {
        UnivariatePolynomialZp64 irreducible = UnivariatePolynomialZ64.create(1, 1, 0, 1).modulus(2);
        FiniteField<UnivariatePolynomialZp64> domain = new FiniteField<>(irreducible);
        UnivariatePolynomial<UnivariatePolynomialZp64> poly =
                UnivariatePolynomial.create(domain,
                        UnivariatePolynomialZ64.create(0, 0, 1).modulus(2),
                        UnivariatePolynomialZ64.create(0, 1, 1).modulus(2),
                        UnivariatePolynomialZ64.create(0, 0, 1).modulus(2),
                        UnivariatePolynomialZ64.create(1).modulus(2),
                        UnivariatePolynomialZ64.create(0, 0, 1).modulus(2),
                        UnivariatePolynomialZ64.create(0).modulus(2),
                        UnivariatePolynomialZ64.create(1, 0, 1).modulus(2),
                        UnivariatePolynomialZ64.create(0, 0, 1).modulus(2));

        PolynomialFactorDecomposition<UnivariatePolynomial<UnivariatePolynomialZp64>> factors = UnivariateSquareFreeFactorization.SquareFreeFactorization(poly);
        assertFactorization(poly, factors);
    }

    @Test
    public void test12() throws Exception {
        for (int i = 1; i < 11; i++) {
            UnivariatePolynomialZ64 poly = UnivariatePolynomialZ64.monomial(1, i);
            PolynomialFactorDecomposition<UnivariatePolynomialZ64> fct = SquareFreeFactorization(poly);
            assertEquals(1, fct.size());
            assertEquals(i, fct.getExponent(0));
            assertEquals(1, fct.get(0).degree);

            PolynomialFactorDecomposition<UnivariatePolynomialZp64> mfct = SquareFreeFactorization(poly.modulus(2));
            assertEquals(1, mfct.size());
            assertEquals(i, mfct.getExponent(0));
            assertEquals(1, mfct.get(0).degree);
        }
    }
}