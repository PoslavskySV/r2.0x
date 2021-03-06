package cc.redberry.rings.poly.univar;

import cc.redberry.libdivide4j.FastDivision;
import cc.redberry.rings.IntegersZp;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.util.ArraysUtil;
import cc.redberry.rings.util.RandomUtil;
import cc.redberry.rings.util.TimeUnits;
import org.apache.commons.math3.random.RandomDataGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.Assert;
import org.junit.Test;

import java.util.Arrays;

import static cc.redberry.libdivide4j.FastDivision.modSignedFast;
import static cc.redberry.rings.poly.univar.UnivariateInterpolation.interpolateNewton;
import static org.junit.Assert.assertEquals;

/**
 * @since 1.0
 */
public class UnivariateInterpolationTest extends AUnivariateTest {
    @Test
    public void test1() throws Exception {
        long
                modulus = 17,
                points[] = {0, 1, 2},
                values[] = {1, 2, 3};
        UnivariatePolynomialZp64 expected = UnivariatePolynomialZ64.create(1, 1).modulus(modulus);
        Assert.assertEquals(expected, UnivariateInterpolation.interpolateLagrange(modulus, points, values));
        Assert.assertEquals(expected, UnivariateInterpolation.interpolateNewton(modulus, points, values));
    }

    @Test
    public void test2() throws Exception {
        long
                modulus = 173,
                points[] = {0, 1, 2, 4},
                values[] = {1, 2, 3, 55};
        UnivariatePolynomialZp64 expected = UnivariatePolynomialZ64.create(1, 34, 37, 103).modulus(modulus);
        Assert.assertEquals(expected, UnivariateInterpolation.interpolateLagrange(modulus, points, values));
        Assert.assertEquals(expected, UnivariateInterpolation.interpolateNewton(modulus, points, values));
    }

    @Test
    public void test3_random_performance() throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = getRandomData();
        DescriptiveStatistics lagrange = new DescriptiveStatistics(), newton = new DescriptiveStatistics();
        int nIterations = its(1000, 1000);
        for (int n = 0; n < nIterations; n++) {
            if (nIterations / 10 == n) {
                lagrange.clear();
                newton.clear();
            }
            long[] points = RandomUtil.randomLongArray(rndd.nextInt(15, 25), 0, Short.MAX_VALUE, rnd);
            long[] values = RandomUtil.randomLongArray(points.length, 0, Short.MAX_VALUE, rnd);
            long modulus = getModulusRandom(rndd.nextInt(5, 30));

            FastDivision.Magic magic = FastDivision.magicSigned(modulus);
            for (int i = 0; i < points.length; ++i) {
                points[i] = modSignedFast(points[i], magic);
                values[i] = modSignedFast(values[i], magic);
            }
            points = ArraysUtil.getSortedDistinct(points);
            values = Arrays.copyOf(values, points.length);

            long start;
            start = System.nanoTime();
            UnivariatePolynomialZp64 pLagrange = UnivariateInterpolation.interpolateLagrange(modulus, points, values);
            lagrange.addValue(System.nanoTime() - start);

            start = System.nanoTime();
            UnivariatePolynomialZp64 pNewton = UnivariateInterpolation.interpolateNewton(modulus, points, values);
            newton.addValue(System.nanoTime() - start);
            assertEquals(pLagrange, pNewton);
            assertInterpolation(pLagrange, points, values);
        }

        System.out.println("Lagrange : " + TimeUnits.statisticsNanotime(lagrange));
        System.out.println("Newton   : " + TimeUnits.statisticsNanotime(newton));
    }

    @Test
    public void test4_random() throws Exception {
        RandomGenerator rnd = getRandom();
        RandomDataGenerator rndd = getRandomData();
        DescriptiveStatistics lagrange = new DescriptiveStatistics(), newton = new DescriptiveStatistics();
        int nIterations = its(100, 1000);
        for (int n = 0; n < nIterations; n++) {
            if (nIterations / 10 == n) {
                lagrange.clear();
                newton.clear();
            }
            BigInteger[] points = RandomUtil.randomBigIntegerArray(rndd.nextInt(15, 25), BigInteger.ZERO, BigInteger.SHORT_MAX_VALUE, rnd);
            BigInteger[] values = RandomUtil.randomBigIntegerArray(points.length, BigInteger.ZERO, BigInteger.SHORT_MAX_VALUE, rnd);
            BigInteger modulus = BigInteger.valueOf(getModulusRandom(rndd.nextInt(5, 30)));

            for (int i = 0; i < points.length; ++i) {
                points[i] = points[i].mod(modulus);
                values[i] = values[i].mod(modulus);
            }
            points = ArraysUtil.getSortedDistinct(points);
            values = Arrays.copyOf(values, points.length);

            long start = System.nanoTime();
            UnivariatePolynomial<BigInteger> pNewton = interpolateNewton(new IntegersZp(modulus), points, values);
            newton.addValue(System.nanoTime() - start);
            assertInterpolation(pNewton, points, values);
        }

        System.out.println("Newton   : " + TimeUnits.statisticsNanotime(newton));
    }

    private static void assertInterpolation(UnivariatePolynomialZp64 poly, long[] points, long[] values) {
        for (int i = 0; i < points.length; i++)
            assertEquals(values[i], poly.evaluate(points[i]));
    }

    private static <E> void assertInterpolation(UnivariatePolynomial<E> poly, E[] points, E[] values) {
        for (int i = 0; i < points.length; i++)
            assertEquals(values[i], poly.evaluate(points[i]));
    }
}