package cc.redberry.rings.poly.univar;

import cc.redberry.rings.IntegersZp;
import cc.redberry.rings.Rational;
import cc.redberry.rings.Rings;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.MachineArithmetic;
import cc.redberry.rings.poly.univar.UnivariateGCD.*;
import cc.redberry.rings.test.Benchmark;
import cc.redberry.rings.util.RandomDataGenerator;
import cc.redberry.rings.util.TimeUnits;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static cc.redberry.rings.poly.univar.RandomUnivariatePolynomials.randomPoly;
import static cc.redberry.rings.poly.univar.UnivariateDivision.divideAndRemainder;
import static cc.redberry.rings.poly.univar.UnivariateGCD.*;
import static org.junit.Assert.*;

/**
 * Created by poslavsky on 15/02/2017.
 */
public class UnivariateGCDTest extends AUnivariateTest {
    @SuppressWarnings("ConstantConditions")
    @Test
    public void test1() throws Exception {
        long modulus = 11;
        UnivariatePolynomialZp64 a = UnivariatePolynomialZ64.create(3480, 8088, 8742, 13810, 12402, 10418, 8966, 4450, 950).modulus(modulus);
        UnivariatePolynomialZp64 b = UnivariatePolynomialZ64.create(2204, 2698, 3694, 3518, 5034, 5214, 5462, 4290, 1216).modulus(modulus);

        PolynomialRemainders<UnivariatePolynomialZp64> prs = UnivariateGCD.EuclidRemainders(a, b);
        UnivariatePolynomialZp64 gcd = prs.gcd();
        assertEquals(3, gcd.degree);
        assertTrue(divideAndRemainder(a, gcd, true)[1].isZero());
        assertTrue(divideAndRemainder(b, gcd, true)[1].isZero());
    }

    @Test
    public void test2() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(0, 14, 50, 93, 108, 130, 70);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(63, 92, 143, 245, 146, 120, 90);
        UnivariatePolynomialZ64 gcd = PseudoRemainders(dividend, divider, true).gcd();
        UnivariatePolynomialZ64 expected = UnivariatePolynomialZ64.create(7, 4, 10, 10);
        assertEquals(expected, gcd);
    }

    @Test
    public void test3() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(7, -7, 0, 1);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(-7, 0, 3);
        PolynomialRemainders<UnivariatePolynomialZ64> naive = PseudoRemainders(dividend.clone(), divider.clone(), false);
        List<UnivariatePolynomialZ64> expectedNaive = new ArrayList<>();
        expectedNaive.add(dividend);
        expectedNaive.add(divider);
        expectedNaive.add(UnivariatePolynomialZ64.create(63, -42));
        expectedNaive.add(UnivariatePolynomialZ64.create(1L));
        assertEquals(expectedNaive, naive.remainders);

        PolynomialRemainders<UnivariatePolynomialZ64> primitive = PseudoRemainders(dividend.clone(), divider.clone(), true);
        List<UnivariatePolynomialZ64> expectedPrimitive = new ArrayList<>();
        expectedPrimitive.add(dividend);
        expectedPrimitive.add(divider);
        expectedPrimitive.add(UnivariatePolynomialZ64.create(-3, 2));
        expectedPrimitive.add(UnivariatePolynomialZ64.create(1L));
        assertEquals(expectedPrimitive, primitive.remainders);

        PolynomialRemainders<UnivariatePolynomialZ64> subresultant = SubresultantRemainders(dividend.clone(), divider.clone());
        List<UnivariatePolynomialZ64> expectedSubresultant = new ArrayList<>();
        expectedSubresultant.add(dividend);
        expectedSubresultant.add(divider);
        expectedSubresultant.add(UnivariatePolynomialZ64.create(63, -42));
        expectedSubresultant.add(UnivariatePolynomialZ64.create(-49L));
        assertEquals(expectedSubresultant, subresultant.remainders);
    }

    @Test
    public void test4() throws Exception {
        for (long sign = -1; sign <= 2; sign += 2) {
            UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2).multiply(sign);
            UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(6, 7, 9, 8, 3).multiply(sign);
            PolynomialRemainders<UnivariatePolynomialZ64> subresultant = SubresultantRemainders(dividend, divider);
            List<UnivariatePolynomialZ64> expectedSubresultant = new ArrayList<>();
            expectedSubresultant.add(dividend);
            expectedSubresultant.add(divider);
            expectedSubresultant.add(UnivariatePolynomialZ64.create(159, 112, 192, 164).multiply(sign));
            expectedSubresultant.add(UnivariatePolynomialZ64.create(4928, 3068, 5072).multiply(sign));
            expectedSubresultant.add(UnivariatePolynomialZ64.create(65840, -98972).multiply(sign));
            expectedSubresultant.add(UnivariatePolynomialZ64.create(3508263).multiply(sign));
            assertEquals(expectedSubresultant, subresultant.remainders);
        }
    }

    @Test
    public void test4a() throws Exception {
        for (long sign1 = -1; sign1 <= 2; sign1 += 2)
            for (long sign2 = -1; sign2 <= 2; sign2 += 2) {
                UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(1, 1, 6, -3, 5).multiply(sign1);
                UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(-9, -3, -10, 2, 8).multiply(sign2);
                PolynomialRemainders<UnivariatePolynomialZ64> subresultant = SubresultantRemainders(dividend, divider);
                List<UnivariatePolynomialZ64> expectedSubresultant = new ArrayList<>();
                expectedSubresultant.add(dividend);
                expectedSubresultant.add(divider);
                expectedSubresultant.add(UnivariatePolynomialZ64.create(-53, -23, -98, 34).multiply(sign1 * sign2));
                expectedSubresultant.add(UnivariatePolynomialZ64.create(4344, 3818, 9774));
                expectedSubresultant.add(UnivariatePolynomialZ64.create(-292677, 442825).multiply(sign1 * sign2));
                expectedSubresultant.add(UnivariatePolynomialZ64.create(22860646));
                assertEquals(expectedSubresultant, subresultant.remainders);
            }
    }

    @Test
    public void test5() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2);
        UnivariateGCD.PolynomialRemainders prs = PseudoRemainders(dividend.clone(), dividend.clone(), false);

        assertEquals(2, prs.remainders.size());
        assertEquals(dividend, prs.gcd());
    }

    @Test
    public void test6() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2).multiply(2);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2);
        PolynomialRemainders<UnivariatePolynomialZ64> prs;

        for (boolean prim : new boolean[]{true, false}) {
            prs = PseudoRemainders(dividend.clone(), divider.clone(), prim);
            assertEquals(2, prs.remainders.size());
            assertEquals(divider, prs.gcd());

            prs = PseudoRemainders(divider.clone(), dividend.clone(), prim);
            assertEquals(2, prs.remainders.size());
            assertEquals(divider, prs.gcd());
        }

        prs = SubresultantRemainders(dividend.clone(), divider.clone());
        assertEquals(2, prs.remainders.size());
        assertEquals(divider, prs.gcd());
    }

    @Test
    public void test7() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2).multiply(2);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(7, 4, 10, 10, 0, 2);

        for (UnivariateGCD.PolynomialRemainders prs : runAlgorithms(dividend, divider)) {
            assertEquals(2, prs.remainders.size());
            assertEquals(divider, prs.gcd());
        }

        for (UnivariateGCD.PolynomialRemainders prs : runAlgorithms(divider, dividend)) {
            assertEquals(2, prs.remainders.size());
            assertEquals(divider, prs.gcd());
        }
    }

    @Test
    public void test8() throws Exception {
        //test long overflow
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(1, 1, 1, 1).multiply(2);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(1, 0, 2);

        for (UnivariateGCD.PolynomialRemainders<UnivariatePolynomialZ64> prs : runAlgorithms(dividend, divider))
            assertEquals(0, prs.gcd().degree);
    }

    @Test
    public void test9() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(-58, 81, -29, -77, 81, 42, -38, 48, 94, 6, 55);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(1, 2, 1);
        UnivariatePolynomialZ64 expected = UnivariatePolynomialZ64.create(-58, -35, 75, -54, -102, 127, 127, 14, 152, 242, 161, 116, 55);
        assertEquals(expected, a.multiply(b));
    }

    @Test
    public void testRandom1() throws Exception {
        RandomGenerator rnd = getRandom();
        for (int i = 0; i < its(100, 1000); i++) {
            UnivariatePolynomialZ64 dividend = RandomUnivariatePolynomials.randomPoly(5, rnd);
            UnivariatePolynomialZ64 divider = RandomUnivariatePolynomials.randomPoly(0, rnd);
            for (UnivariateGCD.PolynomialRemainders<UnivariatePolynomialZ64> prs : runAlgorithms(dividend, divider)) {
                assertEquals(0, prs.gcd().degree);
            }
        }
    }

    @Test
    public void testRandom2() throws Exception {
        RandomGenerator rnd = getRandom();
        int overflows = 0;
        int nIterations = its(10000, 10000);
        for (int i = 0; i < nIterations; i++) {
            UnivariatePolynomialZ64 dividend = RandomUnivariatePolynomials.randomPoly(5, 5, rnd);
            UnivariatePolynomialZ64 divider = RandomUnivariatePolynomials.randomPoly(5, 5, rnd);
            try {
                for (UnivariateGCD.PolynomialRemainders prs :
                        runAlgorithms(dividend, divider,
                                GCDAlgorithm.PolynomialPrimitiveEuclid,
                                GCDAlgorithm.SubresultantEuclid)) {
                    assertPolynomialRemainders(dividend, divider, prs);
                }
            } catch (ArithmeticException e) {
                if (!e.getMessage().equals("long overflow"))
                    throw e;
                ++overflows;
            }
        }
        assertTrue(overflows <= Math.ceil(nIterations / 1000.));
        if (overflows > 0)
            System.out.println("Overflows: " + overflows);
    }

    @Test
    public void testRandom2a() throws Exception {
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(4, -1, -4, -3, 2, 4);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(-4, 1, 4, 3, -2, -4);
        assertPolynomialRemainders(dividend, divider, UnivariateGCD.PseudoRemainders(dividend, divider, true));
    }

    @Test
    public void testRandom2b() throws Exception {
        UnivariatePolynomialZ64 dividend = UnivariatePolynomialZ64.create(0, 0, 4, 0, 4, 4);
        UnivariatePolynomialZ64 divider = UnivariatePolynomialZ64.create(0, 0, 4, 0, 4, 4);
        assertPolynomialRemainders(dividend, divider, UnivariateGCD.PseudoRemainders(dividend, divider, true));
    }

    @Test
    public void testRandom3() throws Exception {
        RandomGenerator rnd = getRandom();
        for (int i = 0; i < its(500, 3000); i++) {
            UnivariatePolynomialZ64 dividend = RandomUnivariatePolynomials.randomPoly(10, 500, rnd);
            UnivariatePolynomialZ64 divider = RandomUnivariatePolynomials.randomPoly(10, 500, rnd);
            for (long prime : getModulusArray(9, 1, 40)) {
                if (dividend.lc() % prime == 0 || divider.lc() % prime == 0)
                    continue;
                UnivariatePolynomialZp64 a = dividend.modulus(prime);
                UnivariatePolynomialZp64 b = divider.modulus(prime);
                PolynomialRemainders<UnivariatePolynomialZp64> euclid = EuclidRemainders(a, b);
                assertPolynomialRemainders(a, b, euclid);
            }
        }
    }

    @Test
    public void test10() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(1740, 4044, 4371, 6905, 6201, 5209, 4483, 2225, 475);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(1102, 1349, 1847, 1759, 2517, 2607, 2731, 2145, 608);
        assertEquals(UnivariatePolynomialZ64.create(29, 21, 32, 19), ModularGCD(a, b));
    }

    @Test
    public void test11() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(0, 1, 1, -6, 17, -18, 14);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(0, 4, -3, 0, 8, 0, 4);
        assertEquals(UnivariatePolynomialZ64.create(0, 1, -2, 2), ModularGCD(a, b));
    }

    @Test
    public void test12() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(1, 2, 3, 3, 6, 9);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(1, 3, 6, 5, 3);
        assertEquals(UnivariatePolynomialZ64.create(1, 2, 3), ModularGCD(a, b));

        a = UnivariatePolynomialZ64.create(0, 0, 1, 2);
        b = UnivariatePolynomialZ64.create(-1, 0, 4);
        assertEquals(UnivariatePolynomialZ64.create(1, 2), ModularGCD(a, b));
    }

    @Test
    public void test13() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(-1, 0, 4);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(-1, 0, 0, 0, 16);
        UnivariatePolynomialZ64 gcd = ModularGCD(a, b);
        assertEquals(UnivariatePolynomialZ64.create(-1, 0, 4), gcd);
    }

    @Test
    public void test14() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(-1, 0, 4);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(1, -5, 6);
        UnivariatePolynomialZ64 gcd = ModularGCD(a, b);
        assertEquals(UnivariatePolynomialZ64.create(-1, 2), gcd);
    }

    @Test
    @Benchmark(runAnyway = true)
    public void testRandom5() throws Exception {
        RandomGenerator rnd = getRandom();
        int overflow = 0;
        int larger = 0;
        DescriptiveStatistics timings = null;
        for (int k = 0; k < 2; k++) {
            timings = new DescriptiveStatistics();
            for (int i = 0; i < its(5000, 10000); i++) {
                try {
                    UnivariatePolynomialZ64 a = RandomUnivariatePolynomials.randomPoly(1 + rnd.nextInt(7), 100, rnd);
                    UnivariatePolynomialZ64 b = RandomUnivariatePolynomials.randomPoly(1 + rnd.nextInt(6), 100, rnd);
                    UnivariatePolynomialZ64 gcd = RandomUnivariatePolynomials.randomPoly(2 + rnd.nextInt(5), 30, rnd);
                    a = a.multiply(gcd);
                    b = b.multiply(gcd);

                    long start = System.nanoTime();
                    UnivariatePolynomialZ64 mgcd = ModularGCD(a, b);
                    timings.addValue(System.nanoTime() - start);

                    assertFalse(mgcd.isConstant());

                    UnivariatePolynomialZ64[] qr = UnivariateDivision.pseudoDivideAndRemainderAdaptive(mgcd, gcd, true);
                    assertNotNull(qr);
                    assertTrue(qr[1].isZero());
                    UnivariatePolynomialZ64[] qr1 = UnivariateDivision.pseudoDivideAndRemainderAdaptive(mgcd.clone(), gcd, false);
                    assertArrayEquals(qr, qr1);
                    if (!qr[0].isConstant()) ++larger;

                    assertGCD(a, b, mgcd);
                } catch (ArithmeticException e) {++overflow;}
            }
        }
        System.out.println("Overflows: " + overflow);
        System.out.println("Larger gcd: " + larger);
        System.out.println("\nTiming statistics:\n" + timings);
    }


    @Test
    public void test15() throws Exception {
        UnivariatePolynomialZ64 poly = UnivariatePolynomialZ64.create(1, 2, 3, 4, 5, -1, -2, -3, -4, -5);
        assertEquals(0, poly.evaluate(1));
        assertEquals(-3999, poly.evaluate(2));
        assertEquals(1881, poly.evaluate(-2));
        assertEquals(566220912246L, poly.evaluate(-17));
    }

    @Test
    public void test16() throws Exception {
        UnivariatePolynomialZ64 poly = UnivariatePolynomialZ64.create(1, 2, 3, 4, 5, -1, -2, -3, -4, -5);
        poly.multiply(MachineArithmetic.safePow(5, poly.degree));

        assertEquals(3045900, poly.evaluateAtRational(1, 5));
        assertEquals(-74846713560L, poly.evaluateAtRational(13, 5));
        assertEquals(40779736470L, poly.evaluateAtRational(13, -5));

        poly.divideOrNull(MachineArithmetic.safePow(5, poly.degree));
        poly.multiply(512);
        assertEquals(-654063683625L, poly.evaluateAtRational(17, 2));
    }

    @Test(expected = IllegalArgumentException.class)
    public void test17() throws Exception {
        UnivariatePolynomialZ64 poly = UnivariatePolynomialZ64.create(1, 2, 3, 4, 5, -1, -2, -3, -4, -5);
        poly.evaluateAtRational(1, 5);
    }

    @Test
    public void test18() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(8, -2 * 8, 8, 8 * 2);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.zero();
        assertEquals(a, SubresultantRemainders(a, b).gcd());
        assertEquals(a, SubresultantRemainders(b, a).gcd());
        assertEquals(a, PseudoRemainders(a, b, true).gcd());
        assertEquals(a, PseudoRemainders(b, a, true).gcd());
        assertEquals(a, EuclidGCD(a, b));
        assertEquals(a, EuclidGCD(b, a));
        assertEquals(a, PolynomialGCD(a, b));
        assertEquals(a, PolynomialGCD(b, a));
    }

    @Test
    public void test19() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(8, -2 * 8, 8, 8 * 2);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(2);
        assertEquals(b, SubresultantRemainders(a, b).gcd());
        assertEquals(b, SubresultantRemainders(b, a).gcd());
        assertEquals(b, PseudoRemainders(a, b, true).gcd());
        assertEquals(b, PseudoRemainders(b, a, true).gcd());
        assertEquals(b, PseudoRemainders(a, b, false).gcd());
        assertEquals(b, PseudoRemainders(b, a, false).gcd());
        assertEquals(b, EuclidGCD(a, b));
        assertEquals(b, EuclidGCD(b, a));
        assertEquals(b, PolynomialGCD(a, b));
        assertEquals(b, PolynomialGCD(b, a));
    }

    @Test
    public void test20() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(32);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(24);
        UnivariatePolynomialZ64 gcd = UnivariatePolynomialZ64.create(8);
        assertEquals(gcd, PolynomialGCD(a, b));
        assertEquals(gcd, SubresultantRemainders(a, b).gcd());
        assertEquals(gcd, PseudoRemainders(a, b, true).gcd());
        assertEquals(gcd, PseudoRemainders(a, b, false).gcd());
    }

    @SuppressWarnings("unchecked")
    private static void assertGCD(IUnivariatePolynomial a, IUnivariatePolynomial b, IUnivariatePolynomial gcd) {
        IUnivariatePolynomial[] qr;
        for (IUnivariatePolynomial dividend : Arrays.asList(a, b)) {
            qr = UnivariateDivision.pseudoDivideAndRemainder(dividend, gcd, true);
            assertNotNull(qr);
            assertTrue(qr[1].isZero());
        }
    }

    @SuppressWarnings("ConstantConditions")
    private static <T extends IUnivariatePolynomial<T>> void assertPolynomialRemainders(T a, T b, PolynomialRemainders<T> prs) {
        if (a.degree() < b.degree()) {
            assertPolynomialRemainders(b, a, prs);
            return;
        }

        if (!a.isOverField()) {
            a = a.clone().primitivePartSameSign();
            b = b.clone().primitivePartSameSign();
        }
        assertEquals(a, prs.remainders.get(0));
        assertEquals(b, prs.size() == 2 ? prs.gcd().primitivePartSameSign() : prs.remainders.get(1));

        T gcd = prs.gcd().clone();
        if (!a.isOverField())
            gcd = gcd.primitivePart();
        assertTrue(UnivariateDivision.pseudoDivideAndRemainder(a, gcd, true)[1].isZero());
        assertTrue(UnivariateDivision.pseudoDivideAndRemainder(b, gcd, true)[1].isZero());
    }
//
//    @SuppressWarnings("ConstantConditions")
//    private static <T extends IMutablePolynomialZp<T>> void assertPolynomialRemainders(T a, T b, PolynomialRemainders<T> prs) {
//        if (a.degree() < b.degree()) {
//            assertPolynomialRemainders(b, a, prs);
//            return;
//        }
//
//        assertEquals(a, prs.remainders.get(0));
//        assertEquals(b, prs.remainders.get(1));
//
//        T gcd = prs.gcd().clone();
//        assertTrue(UnivariateDivision.divideAndRemainder(a, gcd, true)[1].isZero());
//        assertTrue(UnivariateDivision.divideAndRemainder(b, gcd, true)[1].isZero());
//    }

    private static <T extends IUnivariatePolynomial<T>> List<PolynomialRemainders<T>> runAlgorithms(T dividend, T divider, GCDAlgorithm... algorithms) {
        ArrayList<PolynomialRemainders<T>> r = new ArrayList<>();
        for (GCDAlgorithm algorithm : algorithms)
            r.add(algorithm.gcd(dividend, divider));
        return r;
    }

    private enum GCDAlgorithm {
        PolynomialEuclid,
        PolynomialPrimitiveEuclid,
        SubresultantEuclid;

        <T extends IUnivariatePolynomial<T>> PolynomialRemainders<T> gcd(T dividend, T divider) {
            switch (this) {
                case PolynomialEuclid:
                    return PseudoRemainders(dividend, divider, false);
                case PolynomialPrimitiveEuclid:
                    return PseudoRemainders(dividend, divider, true);
                case SubresultantEuclid:
                    return SubresultantRemainders(dividend, divider);
            }
            throw new IllegalArgumentException();
        }
    }

    @Test
    public void test21() throws Exception {
        UnivariatePolynomialZ64 a = UnivariatePolynomialZ64.create(8, 2, -1, -2, -7);
        UnivariatePolynomialZ64 b = UnivariatePolynomialZ64.create(1, -9, -5, -21);
        assertTrue(ModularGCD(a, b).isOne());
    }

    @Test
    public void test22() throws Exception {
        UnivariatePolynomialZp64 a = UnivariatePolynomialZ64.create(1, 2, 3, 4, 3, 2, 1).modulus(25);
        UnivariatePolynomialZp64 b = UnivariatePolynomialZ64.create(1, 2, 3, 1, 3, 2, 1).modulus(25);
        assertExtendedEuclidGCD(a, b);
    }

    @Test
    public void test23() throws Exception {
        //test long overflow
        UnivariatePolynomial<BigInteger> a = UnivariatePolynomial.create(0, 14, 50, 11233219232222L, 108, 130, 70);
        UnivariatePolynomial<BigInteger> b = UnivariatePolynomial.create(63, 92, 143, 1245222, 146, 120, 90);
        UnivariatePolynomial<BigInteger> gcd1 = UnivariatePolynomial.create(1, 2, 3, 4, 5, 4, 3, 2, 1, -1, -2, -3, -4, -5, -4, -3, -2, -1, 999);
        UnivariatePolynomial<BigInteger> gcd2 = UnivariatePolynomial.create(999999L, 123L, 123L, 342425L, 312L, -12312432423L, 13212123123123L, -123124342345L);
        UnivariatePolynomial<BigInteger> gcd3 = UnivariatePolynomial.create(991999L, 123L, 123L, 342425L, 312L, -12312432423L, 13212123123123L, 123124342345L);
        UnivariatePolynomial<BigInteger> gcd4 = UnivariatePolynomial.create(Long.MAX_VALUE, Long.MAX_VALUE - 1, Long.MAX_VALUE - 2, Long.MAX_VALUE - 3, Long.MAX_VALUE - 4, Long.MAX_VALUE - 5);
        UnivariatePolynomial<BigInteger> gcd = gcd1.multiply(gcd2).multiply(gcd3).multiply(gcd4);

        a = a.multiply(gcd);
        b = b.multiply(gcd);

        UnivariatePolynomial<BigInteger> gcdActual = PseudoRemainders(a, b, false).gcd();
        assertGCD(a, b, gcdActual);

        PolynomialRemainders<UnivariatePolynomial<BigInteger>> prs = SubresultantRemainders(a, b);
        assertPolynomialRemainders(a, b, prs);

        UnivariatePolynomial<BigInteger> gcdSubresultant = prs.gcd();
        assertEquals(gcdActual.degree, gcdSubresultant.degree);

        UnivariatePolynomial<BigInteger> gcdModular = ModularGCD(a, b);
        assertEquals(gcdActual.degree, gcdModular.degree);

        System.out.println(gcdActual.normMax().bitLength());
    }

    @Test
    public void testRandom1_bigPoly() throws Exception {
        RandomGenerator rnd = getRandom();
        for (int i = 0; i < its(100, 1000); i++) {
            UnivariatePolynomial<BigInteger> dividend = RandomUnivariatePolynomials.randomPoly(5, BigInteger.LONG_MAX_VALUE, rnd);
            UnivariatePolynomial<BigInteger> divider = RandomUnivariatePolynomials.randomPoly(0, BigInteger.LONG_MAX_VALUE, rnd);
            for (UnivariateGCD.PolynomialRemainders<UnivariatePolynomial<BigInteger>> prs : runAlgorithms(dividend, divider)) {
                assertEquals(0, prs.gcd().degree);
            }
        }
    }

    @Test
    public void testRandom2_bigPoly() throws Exception {
        RandomGenerator rnd = getRandom();
        for (int i = 0; i < its(20, 100); i++) {
            UnivariatePolynomial<BigInteger> dividend = randomPoly(getRandomData().nextInt(10, 50), BigInteger.LONG_MAX_VALUE.shiftRight(1), rnd);
            UnivariatePolynomial<BigInteger> divider = randomPoly(getRandomData().nextInt(10, 50), BigInteger.LONG_MAX_VALUE.shiftRight(1), rnd);
            for (UnivariateGCD.PolynomialRemainders<UnivariatePolynomial<BigInteger>> prs : runAlgorithms(dividend, divider, GCDAlgorithm.SubresultantEuclid, GCDAlgorithm.PolynomialPrimitiveEuclid)) {
                assertPolynomialRemainders(dividend, divider, prs);
            }
        }
    }

    @Test
    public void testRandom3_bigPoly() throws Exception {
        RandomGenerator rnd = getRandom();
        for (int i = 0; i < its(50, 500); i++) {
            UnivariatePolynomial<BigInteger> dividend = randomPoly(getRandomData().nextInt(10, 30), BigInteger.LONG_MAX_VALUE, rnd);
            UnivariatePolynomial<BigInteger> divider = randomPoly(getRandomData().nextInt(10, 30), BigInteger.LONG_MAX_VALUE, rnd);
            for (BigInteger prime : getProbablePrimesArray(BigInteger.LONG_MAX_VALUE.shiftLeft(10), 10)) {
                if (dividend.lc().mod(prime).isZero() || divider.lc().mod(prime).isZero())
                    continue;
                IntegersZp domain = new IntegersZp(prime);
                UnivariatePolynomial<BigInteger> a = dividend.setRing(domain);
                UnivariatePolynomial<BigInteger> b = divider.setRing(domain);
                PolynomialRemainders<UnivariatePolynomial<BigInteger>> euclid = EuclidRemainders(a, b);
                assertPolynomialRemainders(a, b, euclid);
            }
        }
    }

    @Test
    @Benchmark(runAnyway = true)
    public void testRandom5_bigPoly() throws Exception {
        RandomGenerator rnd = getRandom();
        int overflow = 0;
        int larger = 0;
        DescriptiveStatistics timings = null;
        for (int kk = 0; kk < 2; kk++) {
            timings = new DescriptiveStatistics();
            for (int i = 0; i < its(300, 1000); i++) {
                try {
                    UnivariatePolynomial<BigInteger> a = RandomUnivariatePolynomials.randomPoly(1 + rnd.nextInt(30), BigInteger.LONG_MAX_VALUE, rnd);
                    UnivariatePolynomial<BigInteger> b = RandomUnivariatePolynomials.randomPoly(1 + rnd.nextInt(30), BigInteger.LONG_MAX_VALUE, rnd);
                    UnivariatePolynomial<BigInteger> gcd = RandomUnivariatePolynomials.randomPoly(2 + rnd.nextInt(30), BigInteger.LONG_MAX_VALUE, rnd);
                    a = a.multiply(gcd);
                    b = b.multiply(gcd);

                    long start = System.nanoTime();
                    UnivariatePolynomial<BigInteger> mgcd = ModularGCD(a, b);
                    timings.addValue(System.nanoTime() - start);

                    assertFalse(mgcd.isConstant());

                    UnivariatePolynomial<BigInteger>[] qr = UnivariateDivision.pseudoDivideAndRemainder(mgcd, gcd, true);
                    assertNotNull(qr);
                    assertTrue(qr[1].isZero());
                    UnivariatePolynomial<BigInteger>[] qr1 = UnivariateDivision.pseudoDivideAndRemainder(mgcd.clone(), gcd, false);
                    assertArrayEquals(qr, qr1);
                    if (!qr[0].isConstant()) ++larger;

                    assertGCD(a, b, mgcd);
                } catch (ArithmeticException e) {++overflow;}
            }
        }
        System.out.println("Overflows: " + overflow);
        System.out.println("Larger gcd: " + larger);
        System.out.println("\nTiming statistics:\n" + timings);
    }

    @Test
    public void test24() throws Exception {
        long modulus = 419566991;

        UnivariatePolynomial<BigInteger> poly = UnivariatePolynomial.create(Rings.Z, new BigInteger("-4914"), new BigInteger("6213"), new BigInteger("3791"), new BigInteger("996"), new BigInteger("-13304"), new BigInteger("-1567"), new BigInteger("2627"), new BigInteger("15845"), new BigInteger("-12626"), new BigInteger("-6383"), new BigInteger("294"), new BigInteger("26501"), new BigInteger("-17063"), new BigInteger("-14635"), new BigInteger("9387"), new BigInteger("-7141"), new BigInteger("-8185"), new BigInteger("17856"), new BigInteger("4431"), new BigInteger("-13075"), new BigInteger("-7050"), new BigInteger("14672"), new BigInteger("3690"), new BigInteger("-3990"));
        UnivariatePolynomial<BigInteger> a = UnivariatePolynomial.create(Rings.Z, new BigInteger("419563715"), new BigInteger("419566193"), new BigInteger("3612"), new BigInteger("3444"), new BigInteger("419563127"), new BigInteger("419564681"), new BigInteger("419565017"), new BigInteger("419564387"), new BigInteger("419563463"), new BigInteger("3192"), new BigInteger("419563841"), new BigInteger("419563001"));
        UnivariatePolynomial<BigInteger> b = UnivariatePolynomial.create(Rings.Z, new BigInteger("209783497"), new BigInteger("9989688"), new BigInteger("379608231"), new BigInteger("399587609"), new BigInteger("59938143"), new BigInteger("29969072"), new BigInteger("99896901"), new BigInteger("359628849"), new BigInteger("329659781"), new BigInteger("239752567"), new BigInteger("19979379"), new BigInteger("179814423"), new BigInteger("1"));

        IntegersZp domain = new IntegersZp(modulus);
        UnivariatePolynomial<BigInteger> aMod = a.setRing(domain).monic(poly.lc());
        UnivariatePolynomial<BigInteger> bMod = b.setRing(domain).monic();
        UnivariatePolynomial<BigInteger>[] xgcd = UnivariateGCD.ExtendedEuclidGCD(aMod, bMod);
        UnivariatePolynomialZp64[] lxgcd = UnivariateGCD.ExtendedEuclidGCD(UnivariatePolynomial.asOverZp64(aMod), UnivariatePolynomial.asOverZp64(bMod));
        assertEquals(UnivariatePolynomial.asOverZp64(xgcd[0]), lxgcd[0]);
        assertEquals(UnivariatePolynomial.asOverZp64(xgcd[1]), lxgcd[1]);
        assertEquals(UnivariatePolynomial.asOverZp64(xgcd[2]), lxgcd[2]);
    }

    @Test
    public void test25() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.create(Rings.Q,
                Rings.Q.parse("2/3"),
                Rings.Q.parse("4/5"),
                Rings.Q.parse("1/2"),
                Rings.Q.parse("-31/2"));
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.create(Rings.Q,
                Rings.Q.parse("7/3"),
                Rings.Q.parse("4/7"),
                Rings.Q.parse("3/2"),
                Rings.Q.parse("-31/12"));
        UnivariatePolynomial<Rational<BigInteger>> gcd = UnivariatePolynomial.create(Rings.Q,
                Rings.Q.parse("4/3"),
                Rings.Q.parse("-4/7"),
                Rings.Q.parse("-1/2"),
                Rings.Q.parse("-1/12"));
        a = a.clone().multiply(gcd);
        b = b.clone().multiply(gcd);
        assertGCD(a, b, PolynomialGCD(a, b));
    }

    @Test
    public void test26() throws Exception {
        UnivariatePolynomialZp64 a = UnivariatePolynomialZ64.create(1, 2, 3, 1, 2, 3, 4, 3, 2, 1).modulus(29);//.square
        // ().square().square().square().square().square().square().square().square().square();
        UnivariatePolynomialZp64 b = UnivariatePolynomialZ64.create(1, 2, 3, 1, 1, 2, 3, 3).modulus(29);
        assertArrayEquals(ExtendedEuclidGCD(a, b), ExtendedHalfGCD(a, b));
    }

    @Test
    public void test27() throws Exception {
        // assert java heap
        UnivariatePolynomialZp64 a = RandomUnivariatePolynomials.randomMonicPoly(15_000, 19, getRandom());
        UnivariatePolynomialZp64 b = RandomUnivariatePolynomials.randomMonicPoly(15_000, 19, getRandom());
        assertExtendedGCD(ExtendedEuclidGCD(a, b), a, b);
    }

    @Test
    public void test29_randomHalfGCD() throws Exception {
        int
                minimalDegree = UnivariateGCD.SWITCH_TO_HALF_GCD_ALGORITHM_DEGREE,
                maximalDegree = minimalDegree * 4,
                nIterations = its(1000, 10000);
        testHalfGCDRandom(minimalDegree, maximalDegree, nIterations);
    }

    @Benchmark(runAnyway = true)
    @Test
    public void test30_randomHalfGCD() throws Exception {
        int
                minimalDegree = 5 * UnivariateGCD.SWITCH_TO_HALF_GCD_ALGORITHM_DEGREE,
                maximalDegree = minimalDegree * 4,
                nIterations = its(100, 100);
        testHalfGCDRandom(minimalDegree, maximalDegree, nIterations);
    }

    private static void testHalfGCDRandom(int minimalDegree, int maximalDegree, int nIterations) throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = getRandomData();
        DescriptiveStatistics
                euclid = new DescriptiveStatistics(),
                half = new DescriptiveStatistics();
        int nonTrivGCD = 0;
        for (int i = 0; i < nIterations; i++) {
            if (i == nIterations / 10) {
                euclid.clear();
                half.clear();
            }

            long modulus = getModulusRandom(rndd.nextInt(2, 20));
            UnivariatePolynomialZp64 a = RandomUnivariatePolynomials.randomMonicPoly(rndd.nextInt(minimalDegree, maximalDegree), modulus, rnd).multiply(1 + rnd.nextLong());
            UnivariatePolynomialZp64 b = RandomUnivariatePolynomials.randomMonicPoly(rndd.nextInt(minimalDegree, maximalDegree), modulus, rnd).multiply(1 + rnd.nextLong());
            try {
                long start;

                start = System.nanoTime();
                UnivariatePolynomialZp64 expected = EuclidGCD(a, b).monic();
                euclid.addValue(System.nanoTime() - start);

                start = System.nanoTime();
                UnivariatePolynomialZp64 actual = HalfGCD(a, b).monic();
                half.addValue(System.nanoTime() - start);

                assertEquals(expected, actual);

                if (!expected.isConstant())
                    ++nonTrivGCD;
            } catch (Throwable tr) {
                System.out.println("UnivariatePolynomialZ64." + a.toStringForCopy() + ".modulus(" + modulus + ");");
                System.out.println("UnivariatePolynomialZ64." + b.toStringForCopy() + ".modulus(" + modulus + ");");
                throw tr;
            }
        }
        System.out.println("Non-trivial gcds: " + nonTrivGCD);
        System.out.println("Euclid:  " + TimeUnits.statisticsNanotime(euclid));
        System.out.println("HalfGCD: " + TimeUnits.statisticsNanotime(half));
    }

    @Test
    public void test31_randomExtendedHalfGCD() throws Exception {
        int
                minimalDegree = UnivariateGCD.SWITCH_TO_HALF_GCD_ALGORITHM_DEGREE,
                maximalDegree = minimalDegree * 4,
                nIterations = its(1000, 2000);
        testExtendedHalfGCDRandom(minimalDegree, maximalDegree, nIterations);
    }

    @Benchmark(runAnyway = true)
    @Test
    public void test32_randomExtendedHalfGCD() throws Exception {
        int
                minimalDegree = 5 * UnivariateGCD.SWITCH_TO_HALF_GCD_ALGORITHM_DEGREE,
                maximalDegree = minimalDegree * 4,
                nIterations = its(100, 100);
        testExtendedHalfGCDRandom(minimalDegree, maximalDegree, nIterations);
    }

    @Test
    public void test33() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.parse("1 + 23123*x^7 + 2344*x^15", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.parse("1 + 23*x - 23454*x^4", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>>[] xgcd = ModularExtendedGCD(a, b);
        assertExtendedGCD(xgcd, a, b);
    }

    @Test
    public void test33a() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.parse("1 + 23123*x^7 + 2344*x^15", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.parse("1 + 23*x - 23454*x^4", Rings.Q);

        a.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(32)));
        b.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(12332)));

        assertExtendedGCD(ModularExtendedGCD(a, b), a, b);
        assertExtendedGCD(ModularExtendedGCD(b, a), b, a);
    }

    @Test
    public void test34() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.parse("1 + 23123*x^7 + 2344*x^15", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.parse("1 + 23*x - 23454*x^4", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> g = UnivariatePolynomial.parse("1 + (23/2)*x - 23454*x^3", Rings.Q);

        a.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(32)));
        b.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(12332)));

        a.multiply(g);
        b.multiply(g);

        assertExtendedGCD(ModularExtendedGCD(a, b), a, b);
        assertExtendedGCD(ModularExtendedGCD(b, a), b, a);
    }

    @Test
    @Benchmark
    public void test35_performance() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.parse("1 + 23123*x^7 + 2344*x^15", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.parse("1 + 23*x + 23454*x^4", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> g = UnivariatePolynomial.parse("1 + (23/2)*x + 23454*x^3", Rings.Q);

        a.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(32)));
        b.multiply(new Rational<>(Rings.Z, BigInteger.valueOf(123), BigInteger.valueOf(12332)));

        a.multiply(g);
        b.multiply(g);

        System.out.println(a);
        System.out.println(b);
        for (int i = 0; i < 1000; i++) {
            long start = System.nanoTime();
            assertExtendedGCD(ModularExtendedGCD(a, b), a, b);
            assertExtendedGCD(ModularExtendedGCD(b, a), b, a);
            System.out.println(TimeUnits.nanosecondsToString(System.nanoTime() - start));
        }
    }

    @Test
    @Benchmark
    public void test36_performance() throws Exception {
        UnivariatePolynomial<Rational<BigInteger>> a = UnivariatePolynomial.parse("(296/15) + (874/9)*x + (2083/20)*x^2 + ((-11819)/90)*x^3 + ((-147)/8)*  x^4 + (152461/360)*x^5 + (223567/1440)*x^6 + (22223/432)*  x^7 + ((-583021)/2880)*x^8 + (45407/240)*x^9 + (235373/1260)*  x^10 + ((-58349)/378)*x^11 + (269417/2520)*x^12 + (2402/45)*  x^13 + (206113/420)*x^14 + ((-218167)/1890)*x^15 + ((-62221)/5040)*  x^16 + ((-59279)/2520)*x^17 + (164803/630)*x^18 + (1027/54)*  x^19 + ((-539)/30)*x^20 + ((-97)/3)*x^21 + (64/3)*x^22", Rings.Q);
        UnivariatePolynomial<Rational<BigInteger>> b = UnivariatePolynomial.parse("(388/15) + 221*x + (76253/120)*x^2 + (73661/120)*x^3 + ((-21007)/240)* x^4 + (58939/720)*x^5 + (3215/8)*x^6 + (2599/6)*x^7 + (29683/105)* x^8 + ((-7141)/105)*x^9 + (16021/84)*x^10 + (8807/240)* x^11 + (20747/168)*x^12 + ((-1597627)/10080)*x^13 + (1846219/3360)* x^14 + (334471/6720)*x^15 + ((-644489)/6720)*x^16 + ((-551)/20)* x^17 + (17611/120)*x^18 + (3127/30)*x^19 + ((-4591)/120)* x^20 + (229/30)*x^21 + ((-34)/3)*x^22 + (26/3)*x^23", Rings.Q);

        for (int i = 0; i < 1000; i++) {
            long start = System.nanoTime();
            UnivariatePolynomial<Rational<BigInteger>>[] r = ModularExtendedGCD(a, b);
            System.out.println(TimeUnits.nanosecondsToString(System.nanoTime() - start));
            assertExtendedGCD(r, a, b);
        }
    }

    @Test
    public void test36_modularExtendedGCDRandom() throws Exception {
        int nIterations = its(100, 300);
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = getRandomData();
        BigInteger bound = BigInteger.valueOf(100);
        for (int i = 0; i < nIterations; i++) {
            if (i % 50 == 0)
                System.out.println("=> " + i);
            UnivariatePolynomial<BigInteger>
                    a = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(5, 15), bound, rnd),
                    b = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(5, 15), bound, rnd),
                    g = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(1, 15), bound, rnd);

            UnivariatePolynomial<Rational<BigInteger>> ar = a.mapCoefficients(Rings.Q, c -> new Rational<>(Rings.Z, c, BigInteger.valueOf(rndd.nextInt(2, 10))));
            UnivariatePolynomial<Rational<BigInteger>> br = b.mapCoefficients(Rings.Q, c -> new Rational<>(Rings.Z, c, BigInteger.valueOf(rndd.nextInt(2, 10))));
            UnivariatePolynomial<Rational<BigInteger>> gr = g.mapCoefficients(Rings.Q, c -> new Rational<>(Rings.Z, c, BigInteger.valueOf(rndd.nextInt(2, 10))));

            ar.multiply(gr);
            br.multiply(gr);

            UnivariatePolynomial<Rational<BigInteger>>[] xgcd = assertExtendedGCD(ar, br);
            assertTrue(g.degree <= xgcd[0].degree);
            assertExtendedGCD(ar.increment(), br);
        }
    }

    private static void testExtendedHalfGCDRandom(int minimalDegree, int maximalDegree, int nIterations) throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = getRandomData();
        DescriptiveStatistics
                euclid = new DescriptiveStatistics(),
                half = new DescriptiveStatistics();
        int nonTrivGCD = 0;
        for (int i = 0; i < nIterations; i++) {
            if (i == nIterations / 10) {
                euclid.clear();
                half.clear();
            }

            long modulus = getModulusRandom(rndd.nextInt(2, 20));
            UnivariatePolynomialZp64 a = RandomUnivariatePolynomials.randomMonicPoly(rndd.nextInt(minimalDegree, maximalDegree),
                    modulus, rnd).multiply(1 + rnd.nextLong());
            UnivariatePolynomialZp64 b = RandomUnivariatePolynomials.randomMonicPoly(rndd.nextInt(minimalDegree, maximalDegree),
                    modulus, rnd).multiply(1 + rnd.nextLong());
            try {
                long start;

                start = System.nanoTime();
                UnivariatePolynomialZp64[] expected = ExtendedEuclidGCD(a, b);
                euclid.addValue(System.nanoTime() - start);

                start = System.nanoTime();
                UnivariatePolynomialZp64[] actual = ExtendedHalfGCD(a, b);
                half.addValue(System.nanoTime() - start);

                assertArrayEquals(expected, actual);

                if (!expected[0].isConstant())
                    ++nonTrivGCD;
            } catch (Throwable tr) {
                System.out.println("UnivariatePolynomialZ64." + a.toStringForCopy() + ".modulus(" + modulus + ");");
                System.out.println("UnivariatePolynomialZ64." + b.toStringForCopy() + ".modulus(" + modulus + ");");
                throw tr;
            }
        }
        System.out.println("Non-trivial gcds: " + nonTrivGCD);
        System.out.println("Euclid:  " + TimeUnits.statisticsNanotime(euclid));
        System.out.println("HalfGCD: " + TimeUnits.statisticsNanotime(half));
    }

    static <T extends IUnivariatePolynomial<T>> void assertExtendedEuclidGCD(T a, T b) {
        assertExtendedGCD(ExtendedEuclidGCD(a, b), a, b);
    }

    static <T extends IUnivariatePolynomial<T>> T[] assertExtendedGCD(T a, T b) {
        T[] eea = PolynomialExtendedGCD(a, b);
        assertExtendedGCD(eea, a, b);
        return eea;
    }

    static <T extends IUnivariatePolynomial<T>> void assertExtendedGCD(T[] eea, T a, T b) {
        assertEquals(eea[0], a.clone().multiply(eea[1]).add(b.clone().multiply(eea[2])));
        assertEquals(eea[0].degree(), PolynomialGCD(a, b).degree());
    }
}