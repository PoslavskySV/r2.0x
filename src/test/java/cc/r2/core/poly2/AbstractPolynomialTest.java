package cc.r2.core.poly2;

import cc.r2.core.number.primes.BigPrimes;
import cc.r2.core.test.AbstractTest;
import cc.r2.core.test.TimeConsuming;
import org.junit.Assert;
import org.junit.Test;

/**
 * @author Stanislav Poslavsky
 * @since 1.0
 */
public class AbstractPolynomialTest extends AbstractTest {

    protected long getModulusRandom(int nBits) {
        if (nBits <= 1 && nBits > LongModularArithmetics.MAX_SUPPORTED_MODULUS_BITS)
            throw new IllegalArgumentException();
        return BigPrimes.nextPrime(getRandomData().nextLong(1L << (nBits - 1), (1L << nBits) - 1));
    }

    protected long[] getSmallModulusArray(int n) {
        return getModulusArray(n, 0, 0);
    }

    protected long[] getLargeModulusArray(int n, int maxModulusBits) {
        return getModulusArray(0, n, maxModulusBits);
    }

    protected long[] getModulusArray(int nSmall, int nLarge, int smallModulusBits, int maxModulusBits) {
        long[] res = new long[nSmall + nLarge];
        int i = 0;
        for (; i < nSmall; i++)
            res[i] = getModulusRandom(getRandomData().nextInt(2, smallModulusBits));
        for (; i < res.length; i++)
            res[i] = getModulusRandom(getRandomData().nextInt(32, maxModulusBits));
        return res;
    }

    protected long[] getModulusArray(int nSmall, int nLarge, int maxModulusBits) {
        return getModulusArray(nSmall, nLarge, 31, maxModulusBits);
    }

    protected long[] getOneSmallOneLargeModulus(int maxModulusBits) {
        return getModulusArray(1, 1, maxModulusBits);
    }

    @Test
    @TimeConsuming
    public void test1() throws Exception {
        for (int nBits = 2; nBits < 60; nBits++) {
            for (int i = 0; i < 10; i++) {
                int modulusBits = 64 - Long.numberOfLeadingZeros(getModulusRandom(nBits));
                Assert.assertTrue(nBits <= modulusBits && modulusBits <= nBits + 1);
            }
        }
    }
}
