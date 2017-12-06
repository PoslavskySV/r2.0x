package cc.redberry.rings.poly.univar;

import cc.redberry.rings.IntegersZp;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.PolynomialFactorDecomposition;
import cc.redberry.rings.poly.FactorDecompositionTest;
import cc.redberry.rings.primes.SmallPrimes;
import cc.redberry.rings.test.AbstractTest;
import cc.redberry.rings.test.Benchmark;
import cc.redberry.rings.util.TimeUnits;
import org.apache.commons.math3.random.RandomDataGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.Assert;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @since 1.0
 */
public class HenselLiftingTest extends AUnivariateTest {

    @SuppressWarnings("unchecked")
    private static <PolyZ extends IUnivariatePolynomial<PolyZ>, PolyZp extends IUnivariatePolynomial<PolyZp>>
    PolyZp modulus(PolyZ poly, long modulus) {
        if (poly instanceof UnivariatePolynomial)
            return (PolyZp) ((UnivariatePolynomial) poly).setRing(new IntegersZp(modulus));
        else
            return (PolyZp) ((UnivariatePolynomialZ64) poly).modulus(modulus);
    }

    @SuppressWarnings("unchecked")
    private static <PolyZ extends IUnivariatePolynomial<PolyZ>, PolyZp extends IUnivariatePolynomial<PolyZp>>
    PolyZp modulus(PolyZ poly, BigInteger modulus) {
        if (poly instanceof UnivariatePolynomial)
            return (PolyZp) ((UnivariatePolynomial) poly).setRing(new IntegersZp(modulus));
        else
            return (PolyZp) ((UnivariatePolynomialZ64) poly).modulus(modulus.longValueExact());
    }

    @SuppressWarnings("unchecked")
    private static <PolyZ extends IUnivariatePolynomial<PolyZ>, PolyZp extends IUnivariatePolynomial<PolyZp>>
    HenselLifting.QuadraticLiftAbstract<PolyZp> createQuadraticLift(long modulus, PolyZ poly, PolyZp aFactor, PolyZp bFactor) {
        if (poly instanceof UnivariatePolynomial)
            return (HenselLifting.QuadraticLiftAbstract<PolyZp>) HenselLifting.createQuadraticLift(BigInteger.valueOf(modulus),
                    (UnivariatePolynomial) poly, (UnivariatePolynomial) aFactor, (UnivariatePolynomial) bFactor);
        else
            return (HenselLifting.QuadraticLiftAbstract<PolyZp>) HenselLifting.createQuadraticLift(modulus,
                    (UnivariatePolynomialZ64) poly, (UnivariatePolynomialZp64) aFactor, (UnivariatePolynomialZp64) bFactor);
    }

    @SuppressWarnings("unchecked")
    private static <PolyZ extends IUnivariatePolynomial<PolyZ>, PolyZp extends IUnivariatePolynomial<PolyZp>>
    HenselLifting.LiftableQuintet<PolyZp> createLinearLift(long modulus, PolyZ poly, PolyZp aFactor, PolyZp bFactor) {
        if (poly instanceof UnivariatePolynomial)
            return (HenselLifting.LiftableQuintet<PolyZp>) HenselLifting.createLinearLift(modulus,
                    (UnivariatePolynomial) poly, UnivariatePolynomial.asOverZp64((UnivariatePolynomial) aFactor), UnivariatePolynomial.asOverZp64((UnivariatePolynomial) bFactor));
        else
            return (HenselLifting.LiftableQuintet<PolyZp>) HenselLifting.createLinearLift(modulus,
                    (UnivariatePolynomialZ64) poly, (UnivariatePolynomialZp64) aFactor, (UnivariatePolynomialZp64) bFactor);
    }

    <PolyZ extends IUnivariatePolynomial<PolyZ>, PolyZp extends IUnivariatePolynomial<PolyZp>>
    void testHenselStepRandomModulus(
            PolyZ poly,
            PolyZ aFactor,
            PolyZ bFactor,
            boolean quadratic,
            int nIterations,
            int nPrimes) {

        out:
        for (long modulus : getModulusArray(nPrimes, 0, 5, 0)) {
            PolyZp aMod = modulus(aFactor, modulus);
            PolyZp bMod = modulus(bFactor, modulus);
            if (aMod.degree() != aFactor.degree() || bMod.degree() != bFactor.degree())
                continue;

            if (!UnivariateGCD.PolynomialGCD(aMod, bMod).isConstant())
                continue;
            HenselLifting.LiftableQuintet<PolyZp> hensel =
                    quadratic ? createQuadraticLift(modulus, poly, aMod, bMod) : createLinearLift(modulus, poly, aMod, bMod);
            assertHenselLift(hensel);

            for (int i = 0; i < nIterations - 1; i++) {
                try {
                    hensel.lift();
                } catch (ArithmeticException ex) {
                    if (!"long overflow".equals(ex.getMessage()))
                        throw ex;
                    continue out;
                }
                assertHenselLift(hensel);
            }
            hensel.liftLast();
            assertHenselLift(hensel);
        }
    }

    @Test
    public void testHensel1() throws Exception {
        UnivariatePolynomialZ64 aFactor = UnivariatePolynomialZ64.create(-2, -1, 2, 1);
        UnivariatePolynomialZ64 bFactor = UnivariatePolynomialZ64.create(-2, 1);
        UnivariatePolynomialZ64 poly = aFactor.clone().multiply(bFactor);
        testHenselStepRandomModulus(poly, aFactor, bFactor, true, 10, 20);
        testHenselStepRandomModulus(poly, aFactor, bFactor, false, 10, 20);
    }

    @Test
    public void testHensel2() throws Exception {
        UnivariatePolynomialZ64 aFactor = UnivariatePolynomialZ64.create(3, 1);
        UnivariatePolynomialZ64 bFactor = UnivariatePolynomialZ64.create(4, 1);
        UnivariatePolynomialZ64 poly = aFactor.clone().multiply(bFactor);
        testHenselStepRandomModulus(poly, aFactor, bFactor, true, 10, 20);
        testHenselStepRandomModulus(poly, aFactor, bFactor, false, 10, 20);
    }

    @Test
    public void testHensel3() throws Exception {
        UnivariatePolynomialZ64 aFactor = UnivariatePolynomialZ64.create(12, 13112, 1112, 31, 112);
        UnivariatePolynomialZ64 bFactor = UnivariatePolynomialZ64.create(22, 112311, 12);
        UnivariatePolynomialZ64 poly = aFactor.clone().multiply(bFactor);

        testHenselStepRandomModulus(poly, aFactor, bFactor, true, 10, 20);
        testHenselStepRandomModulus(poly, aFactor, bFactor, false, 10, 20);
    }

    @Test
    public void testHensel4_random() throws Exception {
        RandomGenerator rnd = AbstractTest.getRandom();
        RandomDataGenerator rndd = AbstractTest.getRandomData();
        int nIterations = (int) AbstractTest.its(100, 1000);
        for (int i = 0; i < nIterations; i++) {
            UnivariatePolynomial<BigInteger> a = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(2, 5), BigInteger.INT_MAX_VALUE, rnd);
            UnivariatePolynomial<BigInteger> b = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(2, 5), BigInteger.INT_MAX_VALUE, rnd);
            UnivariatePolynomial<BigInteger> poly = a.clone().multiply(b);
            testHenselStepRandomModulus(poly, a, b, true, 5, 5);
            testHenselStepRandomModulus(poly, a, b, false, 5, 5);
        }
    }

    static void testMultiFactorHenselLifting(UnivariatePolynomial<BigInteger> base, long modulus, int nIterations, boolean quadratic) {
        base = UnivariateSquareFreeFactorization.SquareFreePart(base);

        UnivariatePolynomialZp64 baseMod = UnivariatePolynomial.asOverZp64(base.setRing(new IntegersZp(modulus)));
        if (baseMod.degree() != base.degree())
            return;

        if (!UnivariateSquareFreeFactorization.isSquareFree(baseMod))
            return;

        PolynomialFactorDecomposition<UnivariatePolynomialZp64> modularFactors = UnivariateFactorization.FactorInGF(baseMod);
        FactorDecompositionTest.assertFactorization(baseMod, modularFactors);

        HenselLifting.LiftFactory<UnivariatePolynomialZp64> factory = quadratic ? HenselLifting::createQuadraticLift : HenselLifting::createLinearLift;
        BigInteger newModulus = newModulus(modulus, nIterations, quadratic);
        List<UnivariatePolynomial<BigInteger>> tmp = HenselLifting.liftFactorization0(BigInteger.valueOf(modulus), newModulus, nIterations, base, modularFactors.factors, factory);
        UnivariatePolynomial<BigInteger> bm = base.setRing(new IntegersZp(newModulus));
        FactorizationTestUtil.assertFactorization(bm, bm.lc(), tmp);
    }

    static BigInteger newModulus(long modulus, int nIterations, boolean quadratic) {
        BigInteger result, bModulus = result = BigInteger.valueOf(modulus);
        for (int i = 0; i < nIterations; i++)
            result = result.multiply(quadratic ? result : bModulus);
        return result;
    }

    static void testMultiFactorHenselLifting(UnivariatePolynomial<BigInteger> base, long modulus, boolean quadratic) {
        testMultiFactorHenselLifting(base, modulus, HenselLifting.nIterations(BigInteger.valueOf(modulus), UnivariatePolynomial.mignotteBound(base).shiftLeft(1), quadratic).nIterations, quadratic);
    }

    static void testMultiFactorHenselLifting(UnivariatePolynomial<BigInteger> base, long modulus) {
        testMultiFactorHenselLifting(base, modulus, true);
        testMultiFactorHenselLifting(base, modulus, false);
    }

    @Test
    public void testHensel5() throws Exception {
        UnivariatePolynomial<BigInteger> base = UnivariatePolynomial.create(1, 2, 3, 4, 1, 6, 7, 1, 5, 4, 3, 2, 1);
        testMultiFactorHenselLifting(base, 5, 5, true);
        testMultiFactorHenselLifting(base, 5, 5, false);
    }

    @Test
    public void testHensel6() throws Exception {
        UnivariatePolynomial<BigInteger> base = UnivariatePolynomial.create(1, 2, 3, 4, 1, 6, 7, 1, 5, 4, 3, 2, 1);
        testMultiFactorHenselLifting(base, 11, 5, true);
        testMultiFactorHenselLifting(base, 11, 5, false);
    }

    @Test
    public void testHensel7_random() throws Exception {
        RandomGenerator rnd = AbstractTest.getRandom();
        RandomDataGenerator rndd = AbstractTest.getRandomData();
        for (int i = 0; i < AbstractTest.its(100, 1000); ++i) {
            UnivariatePolynomial<BigInteger> poly = RandomUnivariatePolynomials.randomPoly(rndd.nextInt(5, 15), BigInteger.LONG_MAX_VALUE, rnd);
            for (long modulus : getModulusArray((int) AbstractTest.its(5, 15), 0, 5, 0)) {
                UnivariatePolynomialZp64 polyMod = UnivariatePolynomial.asOverZp64(poly.setRing(new IntegersZp(modulus)));
                if (polyMod.isConstant() || polyMod.isMonomial())
                    continue;

                while (poly.lc().mod(BigInteger.valueOf(modulus)).isZero())
                    poly.data[poly.degree] = BigInteger.valueOf(rnd.nextInt());

                try {
                    testMultiFactorHenselLifting(poly, modulus);
                } catch (AssertionError err) {
                    System.out.println(poly.toStringForCopy());
                    System.out.println(modulus);
                    throw err;
                }
            }
        }
    }

    @Test
    @Benchmark
    public void testHensel8_linear_vs_quadratic() throws Exception {
        long modulus = SmallPrimes.nextPrime(2132131231);
        RandomGenerator rnd = AbstractTest.getRandom();
        UnivariatePolynomial<BigInteger> aFactor, bFactor;
        IntegersZp domain = new IntegersZp(modulus);
        do {
            aFactor = RandomUnivariatePolynomials.randomPoly(5, BigInteger.LONG_MAX_VALUE, rnd);
            bFactor = RandomUnivariatePolynomials.randomPoly(5, BigInteger.LONG_MAX_VALUE, rnd);
        } while (!UnivariateGCD.PolynomialGCD(aFactor.setRing(domain), bFactor.setRing(domain)).isConstant());

        UnivariatePolynomial<BigInteger> poly = aFactor.clone().multiply(bFactor);

        int nTrials = 20;
        int maxIterations;
        HenselLifting.LiftableQuintet<UnivariatePolynomial<BigInteger>> linearLift, quadraticLift;
        DescriptiveStatistics acc = new DescriptiveStatistics();

        List<double[]> linear = new ArrayList<>(), quadratic = new ArrayList<>();

        //warm-up
        for (int j = 0; j < 64; j++) {
            linearLift = createLinearLift(modulus, poly, aFactor.setRing(domain), bFactor.setRing(domain));
            linearLift.lift(j);
        }

        maxIterations = 12 * 12;
        for (int nIts = 1; nIts < maxIterations; nIts++) {
            System.out.println(nIts);
            acc.clear();
            for (int j = 0; j < nTrials; j++) {
                long start = System.nanoTime();
                linearLift = createLinearLift(modulus, poly, aFactor.setRing(domain), bFactor.setRing(domain));
                linearLift.lift(nIts);
                acc.addValue(System.nanoTime() - start);
                assertHenselLift(linearLift);
            }
            linear.add(new double[]{nIts, acc.getPercentile(0.5), acc.getStandardDeviation()});
        }


        //warm-up
        for (int j = 0; j < 6; j++) {
            quadraticLift = createQuadraticLift(modulus, poly, aFactor.setRing(domain), bFactor.setRing(domain));
            quadraticLift.lift(j);
        }

        maxIterations = 12;
        for (int nIts = 1; nIts < maxIterations; nIts++) {
            System.out.println(nIts);
            acc.clear();
            for (int j = 0; j < nTrials; j++) {
                long start = System.nanoTime();
                quadraticLift = createQuadraticLift(modulus, poly, aFactor.setRing(domain), bFactor.setRing(domain));
                quadraticLift.lift(nIts);
                acc.addValue(System.nanoTime() - start);
                assertHenselLift(quadraticLift);
            }
            quadratic.add(new double[]{nIts, acc.getPercentile(0.5), acc.getStandardDeviation()});
        }

        System.out.println("linear = " + toString(linear) + ";");
        System.out.println("quadratic = " + toString(quadratic) + ";");
    }

    private static String toString(List<double[]> d) {
        StringBuilder sb = new StringBuilder().append("{");
        for (int i = 0; ; i++) {
            sb
                    .append("{")
                    .append(Arrays.stream(d.get(i)).mapToObj(Double::toString).collect(Collectors.joining(",")))
                    .append("}");
            if (i == d.size() - 1)
                break;
            sb.append(",");
        }
        sb.append("}");
        return sb.toString();
    }


    @Test
    @Benchmark(runAnyway = true)
    public void testHensel9_random() throws Exception {
        RandomGenerator rnd = AbstractTest.getRandom();
        RandomDataGenerator rndd = AbstractTest.getRandomData();
        DescriptiveStatistics
                linear = new DescriptiveStatistics(),
                quadratic = new DescriptiveStatistics(),
                adaptive = new DescriptiveStatistics();

        int nFactors = 6;
        int nIterations = (int) AbstractTest.its(30, 150);
        for (int n = 0; n < nIterations; n++) {
            if (nIterations / 10 == n) {
                linear.clear();
                quadratic.clear();
                adaptive.clear();
            }
            if (n % 10 == 0)
                System.out.println(n);

            UnivariatePolynomial<BigInteger> poly = UnivariatePolynomial.create(1);
            for (int i = 0; i < nFactors; i++)
                poly = poly.multiply(RandomUnivariatePolynomials.randomPoly(rndd.nextInt(5, 15), BigInteger.valueOf(1000), rnd));
            poly = UnivariateSquareFreeFactorization.SquareFreePart(poly);

            UnivariatePolynomial<BigInteger> polyMod;
            long modulus;
            IntegersZp domain;
            do {
                modulus = getModulusRandom(rndd.nextInt(5, 28));
                domain = new IntegersZp(modulus);
                polyMod = poly.setRing(domain);
            }
            while (!UnivariateSquareFreeFactorization.isSquareFree(poly.setRing(domain)) || polyMod.degree() != poly.degree());

            BigInteger desiredBound = UnivariatePolynomial.mignotteBound(poly).shiftLeft(1).multiply(poly.lc());
            PolynomialFactorDecomposition<UnivariatePolynomialZp64> modularFactors = UnivariateFactorization.FactorInGF(UnivariatePolynomial.asOverZp64(polyMod));
            BigInteger bModulus = BigInteger.valueOf(modulus);

            long start;
            try {
                start = System.nanoTime();
                List<UnivariatePolynomial<BigInteger>> factorsQuad = HenselLifting.liftFactorization(bModulus, desiredBound, poly, modularFactors.factors, true);
                quadratic.addValue(System.nanoTime() - start);
                FactorizationTestUtil.assertFactorization(poly.setRing(factorsQuad.get(0).ring), poly.lc(), factorsQuad);

                start = System.nanoTime();
                List<UnivariatePolynomial<BigInteger>> factorsLin = HenselLifting.liftFactorization(bModulus, desiredBound, poly, modularFactors.factors, false);
                linear.addValue(System.nanoTime() - start);
                FactorizationTestUtil.assertFactorization(poly.setRing(factorsLin.get(0).ring), poly.lc(), factorsLin);


                start = System.nanoTime();
                List<UnivariatePolynomial<BigInteger>> factorsAdp = HenselLifting.liftFactorization(bModulus, desiredBound, poly, modularFactors.factors);
                adaptive.addValue(System.nanoTime() - start);
                FactorizationTestUtil.assertFactorization(poly.setRing(factorsAdp.get(0).ring), poly.lc(), factorsAdp);
            } catch (Throwable e) {
                System.out.println("====");
                System.out.println(modulus);
                System.out.println(poly);
                System.out.println(modularFactors);
                System.out.println(poly.toStringForCopy());
                System.out.println("====");
                throw e;
            }
        }

        System.out.println("Quadratic lifting : " + TimeUnits.statisticsNanotime(quadratic, true));
        System.out.println("Linear lifting   : " + TimeUnits.statisticsNanotime(linear, true));
        System.out.println("Adaptive lifting   : " + TimeUnits.statisticsNanotime(adaptive, true));
    }

    private static <T extends IUnivariatePolynomial<T>> void assertHenselLift(HenselLifting.LiftableQuintet<T> lift) {
        Assert.assertEquals(lift.toString(), lift.polyMod(), lift.aFactorMod().clone().multiply(lift.bFactorMod()));
        Assert.assertTrue(lift.toString(), lift.aCoFactorMod() == null && lift.bCoFactorMod() == null ||
                lift.aFactorMod().clone().multiply(lift.aCoFactorMod())
                        .add(lift.bFactorMod().clone().multiply(lift.bCoFactorMod()))
                        .isOne());
    }
}