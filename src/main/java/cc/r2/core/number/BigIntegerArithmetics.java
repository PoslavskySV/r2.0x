package cc.r2.core.number;

import static cc.r2.core.number.BigInteger.ONE;

/**
 * @author Stanislav Poslavsky
 * @since 1.0
 */
public final class BigIntegerArithmetics {
    public BigIntegerArithmetics() {}

    public static BigInteger max(BigInteger a, BigInteger b) {
        return a.compareTo(b) > 0 ? a : b;
    }

    public static BigInteger abs(BigInteger a) {
        return a.abs();
    }

    public static BigInteger gcd(BigInteger a, BigInteger b) {
        return a.gcd(b);
    }

    /**
     * Returns the greatest common an array of longs
     *
     * @param integers array of longs
     * @param from     from position (inclusive)
     * @param to       to position (exclusive)
     * @return greatest common divisor of array
     */
    public static BigInteger gcd(final BigInteger[] integers, int from, int to) {
        if (integers.length < 2)
            throw new IllegalArgumentException();
        BigInteger gcd = gcd(integers[from], integers[from + 1]);
        if (gcd.isOne())
            return gcd;
        for (int i = from + 2; i < to; i++) {
            gcd = gcd(integers[i], gcd);
            if (gcd.isOne())
                return gcd;
        }
        return gcd;
    }

    /**
     * Returns {@code base} in a power of {@code e} (non negative)
     *
     * @param base     base
     * @param exponent exponent (non negative)
     * @return {@code base} in a power of {@code e}
     * @throws ArithmeticException if the result overflows a long
     */
    public static BigInteger pow(final BigInteger base, long exponent) {
        if (exponent < 0)
            throw new IllegalArgumentException();

        BigInteger result = ONE;
        BigInteger k2p = base;
        for (; ; ) {
            if ((exponent&1) != 0)
                result = result.multiply(k2p);
            exponent = exponent >> 1;
            if (exponent == 0)
                return result;
            k2p = k2p.multiply(k2p);
        }
    }

    /* ************************ mock methods for @Specialization ************************ */

    public static BigInteger safeAdd(BigInteger a, BigInteger b) {
        return a.add(b);
    }

    public static BigInteger safeSubtract(BigInteger a, BigInteger b) {
        return a.subtract(b);
    }

    public static BigInteger safeMultiply(BigInteger a, BigInteger b) {
        return a.multiply(b);
    }

    public static BigInteger safePow(BigInteger a, long exp) {
        return pow(a, exp);
    }

    public static BigInteger modInverse(BigInteger a, BigInteger mod){
        return a.modInverse(mod);
    }

    public static BigInteger mod(BigInteger a, BigInteger mod){
        return a.mod(mod);
    }
}
