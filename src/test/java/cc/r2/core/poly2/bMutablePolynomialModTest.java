package cc.r2.core.poly2;

import cc.r2.core.number.BigInteger;
import org.junit.Assert;
import org.junit.Test;

/**
 * @author Stanislav Poslavsky
 * @since 1.0
 */
public class bMutablePolynomialModTest {

    @Test
    public void test1() throws Exception {
        bMutablePolynomialZ aZ = bMutablePolynomialZ.create(1, 2, 3, 4, 5, 6);
        BigInteger modulus = BigInteger.valueOf(59);
        bMutablePolynomialMod a = aZ.modulus(modulus);
        MutablePolynomialMod aL = a.toLong();

        for (int i = 0; i < 5; i++) {
            a = (a.clone() * a.clone().decrement() - a.clone().derivative() + (a.clone().square())) * a.clone();
            a = a.truncate(a.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            a = a.add(a.derivative()).decrement();
//            a = a.multiply(a.derivative().increment().truncate(10));

            aZ = (aZ.clone() * aZ.clone().decrement() - aZ.clone().derivative() + (aZ.clone().square())) * aZ.clone();
            aZ = aZ.truncate(aZ.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            aZ = aZ.add(aZ.derivative()).decrement();
//            aZ = aZ.multiply(aZ.derivative().increment().truncate(10));

            aL = (aL.clone() * aL.clone().decrement() - aL.clone().derivative() + (aL.clone().square())) * aL.clone();
            aL = aL.truncate(aL.degree * 3 / 2).shiftRight(2).shiftLeft(2).increment().negate();
            aL = aL.add(aL.derivative()).decrement();
//            aL = aL.multiply(aL.derivative().increment().truncate(10));
        }

        System.out.println(a.degree);
        Assert.assertEquals(aL, a.toLong());
        Assert.assertEquals(a, aZ.modulus(modulus));
    }

    @Test
    public void test2() throws Exception {
        Assert.assertEquals(
                bMutablePolynomialZ.parse("1 + x+ x^23"),
                bMutablePolynomialZ.parse("x+1+x^23"));
    }

    @Test
    public void test3() throws Exception {
        BigInteger modulus = new BigInteger("998427238390739620139");
        bMutablePolynomialMod factory = bMutablePolynomialMod.one(modulus);

        BigInteger a = new BigInteger("213471654376351273471236215473").mod(modulus);
        BigInteger b = new BigInteger("41982734698213476213918476921834").mod(modulus);
        Assert.assertEquals(b.subtract(a).mod(modulus), factory.subtractMod(b, a));
        Assert.assertEquals(a.subtract(b).mod(modulus), factory.subtractMod(a, b));
    }
}