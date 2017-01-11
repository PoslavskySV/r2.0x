package cc.r2.core.polynomial;

import org.apache.commons.math3.random.RandomDataGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well1024a;
import org.junit.Test;

import static cc.r2.core.polynomial.SmallPolynomialArithmetics.*;
import static org.junit.Assert.assertEquals;

public class SmallPolynomialArithmeticsTest {
    @Test
    public void test1() throws Exception {
        MutableLongPoly a = MutableLongPoly.create(1, 4);
        MutableLongPoly b = MutableLongPoly.create(0, 2, 3);
        MutableLongPoly polyModulus = MutableLongPoly.create(0, 4, 0, 1);
        long modulus = 5;
        assertEquals(MutableLongPoly.create(0, 4, 1), polyMultiplyMod(a, b, polyModulus, modulus, true));
        assertEquals(MutableLongPoly.create(0, 4, 1), polyMultiplyMod(a.clone(), b, polyModulus, modulus, false));
    }

    @Test
    public void test2() throws Exception {
        MutableLongPoly a = MutableLongPoly.create(1, 2, 3, 4, 0);
        assertEquals(MutableLongPoly.create(2, 6, 12), derivative(a));
    }

    @Test
    public void test3() throws Exception {
        assertEquals(MutableLongPoly.create(1, 2, 1), polyPow(MutableLongPoly.create(1, 1), 2, true));
        assertEquals(MutableLongPoly.create(1, 2, 1), polyPow(MutableLongPoly.create(1, 1), 2, false));
    }

    @Test
    public void test4() throws Exception {
//        System.out.println(LongArithmetics.modInverse(7, 7));
//        assertEquals(MutableLongPoly.create(1, 2, 1), pow(MutableLongPoly.create(1, 1), 2));
        MutableLongPoly a = MutableLongPoly.create(1, 0, 1, 0, 1);
        MutableLongPoly b = MutableLongPoly.create(1, 1, 1);
        System.out.println(SmallPolynomialArithmetics.polyPowMod(b, 2, 2, true));
    }

    @Test
    public void test5() throws Exception {
        MutableLongPoly a = MutableLongPoly.create(0, 0, 0, 1);
        MutableLongPoly polyModulus = MutableLongPoly.create(0, -1, -1, -1, 0, 1, -1, 1, 1);
        long modulus = 3;
        assertEquals(MutableLongPoly.create(0, -1, 0, 0, 1, 1, 1, -1).modulus(modulus), SmallPolynomialArithmetics.polyPowMod(a, modulus, polyModulus, modulus, true));
        assertEquals(MutableLongPoly.create(0, -1, 0, 0, 1, 1, 1, -1).modulus(modulus), SmallPolynomialArithmetics.polyPowMod(a, modulus, polyModulus, modulus, false));
    }

    @Test
    public void test6() throws Exception {
        RandomGenerator rnd = new Well1024a();
        RandomDataGenerator rndd = new RandomDataGenerator(rnd);
        long[] primes = {2, 3, 5, 7, 11, 17, 67, 29, 31, 89, 101, 107, 139, 223};
        for (int i = 0; i < 100; i++) {
            MutableLongPoly poly = RandomPolynomials.randomPoly(rndd.nextInt(1, 5), 100, rnd);
            MutableLongPoly polyModulus = RandomPolynomials.randomPoly(rndd.nextInt(poly.degree == 1 ? 0 : 1, poly.degree), 100, rnd);
            poly.data[poly.degree] = 1;
            polyModulus.data[polyModulus.degree] = 1;
            int exponent = 2 + rnd.nextInt(20);
            for (long prime : primes) {
                MutableLongPoly base = poly.clone().monic(prime);
                MutableLongPoly modulus = polyModulus.clone().monic(prime);
                assertEquals(polyMod(polyPowMod(base, exponent, prime, true), modulus, prime, false), SmallPolynomialArithmetics.polyPowMod(base, exponent, polyModulus, prime, true));
            }
        }
    }


    @Test
    public void name() throws Exception {
        MutableLongPoly base = MutableLongPoly.create(1245, 4302, 3125, 832, 690, 4922, 1952, 2385, 2656, 5332, 1335, 3167, 3702, 4975, 2105, 1999, 5142, 360, 646, 5002, 797, 744, 5303, 4711, 1973, 1865, 4841, 2281, 1200, 2010, 4943, 5491, 2024, 5558, 4338, 1854, 52, 3516, 276, 1043, 4708, 4658, 1876, 3897, 1389, 4598, 933, 1730, 4767, 3337, 940, 424, 1094, 133, 4219, 4180, 650, 2297, 2048, 3174, 2466, 4310, 2886, 3452, 3287, 1634, 548, 2052, 406, 2000, 1595, 2855, 2478, 3098, 1728, 3663, 5027, 720, 3425, 2224, 94, 2551, 1005, 3043, 914, 4938, 5091, 1417, 1998, 1618, 4784, 5407, 5482, 2464, 4278, 4020, 278, 3513, 3773, 4262, 4221, 133, 4175, 4648, 479, 5415, 4496, 3732, 5126, 3932, 4394, 1378, 4265, 2222, 3464, 4251, 3092, 1208, 1748, 1268, 2438, 3568, 3195, 3020, 15, 4947, 1435, 5223, 4021, 2099, 5237, 5654, 1810, 4221, 3948, 1069, 4686, 3244, 4636, 261, 300, 1658, 4857, 5033, 103, 5019, 1408, 5232, 5594, 5175, 750, 3768, 361, 3608, 1113, 5498, 566, 781, 4315, 1499, 772, 3076, 2685, 5092, 4393, 1892, 2770, 4522, 2890, 4333, 3517, 1652, 27, 3628, 3953, 247, 863, 2878, 4083, 1910, 1356, 3608, 5618, 1201, 5329, 3995, 2155, 4366, 3636, 3722, 1823, 2425, 4118, 3744, 5096, 1870, 1460, 1924, 2802, 1170, 2838, 139, 1939, 3929, 2158, 4873, 2734, 5038, 4791, 2352, 2196, 174, 1100, 621, 4794, 991, 2087, 336, 3507, 5615, 1493, 3914, 624, 161, 504, 2984, 3067, 2559, 3066, 835, 1134, 2816, 3397, 4116, 2514, 4873, 821, 39, 1275, 1468, 3798, 1830, 2673, 1878, 572, 3531, 2008, 803, 2587, 986, 1498, 4764, 2244, 356, 1788, 4455, 4826, 4714, 4, 3015, 1183, 4825, 1321, 2510, 4720, 2307, 1981, 2796, 4722, 4554, 374);
        MutableLongPoly polyModulus = MutableLongPoly.create(991, 951, 5298, 5465, 1419, 4100, 3593, 2165, 2286, 1950, 640, 1878, 1872, 3766, 4964, 4708, 3098, 692, 4274, 573, 3134, 3204, 2146, 4772, 1985, 4392, 2403, 2926, 4287, 4744, 1316, 393, 1822, 2296, 2165, 4158, 2783, 5051, 5301, 4694, 4257, 1188, 4933, 4117, 4046, 3320, 1388, 3176, 1569, 5202, 813, 3275, 1179, 2346, 1422, 1915, 1729, 5300, 3671, 5279, 5519, 5556, 1949, 5543, 3490, 2086, 3336, 5043, 4000, 4629, 4392, 4441, 3585, 462, 5626, 3216, 2317, 3027, 4423, 1302, 5090, 3660, 340, 2101, 4631, 587, 2342, 419, 5516, 1448, 275, 1823, 4271, 5557, 1822, 4458, 4451, 5066, 949, 1717, 2691, 4559, 3795, 3462, 2521, 295, 262, 885, 4752, 270, 4568, 5335, 2042, 3678, 2340, 5576, 263, 5509, 1901, 4528, 4808, 850, 4051, 610, 1605, 2878, 260, 3986, 1194, 2728, 1414, 5036, 4695, 2519, 2026, 5219, 3708, 2790, 3679, 2583, 2440, 2686, 251, 2922, 1395, 35, 2044, 5412, 116, 63, 4527, 4676, 2871, 5565, 3121, 2854, 374, 5043, 5067, 5013, 4181, 4434, 5279, 2184, 558, 92, 490, 4746, 4384, 3855, 2897, 3811, 3652, 1378, 1866, 2712, 3778, 3276, 5069, 1212, 3216, 1251, 3892, 4745, 4235, 2108, 5350, 4802, 3500, 4055, 3553, 898, 4836, 230, 195, 4478, 3167, 3661, 3636, 5601, 2263, 260, 4947, 4619, 859, 4337, 2139, 2172, 472, 5271, 658, 1630, 667, 4044, 2731, 3858, 1354, 3340, 2951, 889, 3087, 3067, 2797, 2432, 2502, 3381, 2182, 1779, 3290, 3604, 3246, 2707, 3876, 5452, 1162, 1920, 2846, 2386, 5005, 5115, 4384, 3406, 3461, 4257, 3700, 1060, 980, 2933, 875, 4035, 2090, 4972, 5392, 5185, 4356, 5441, 2953, 4575, 4403, 1025, 2484, 3957, 3479, 2309, 605, 627, 3999, 2005, 1728, 1133, 4199, 1);
        long modulus = 5659;
        System.out.println(polyModulus.degree);
        System.out.println(base);
        System.out.println(polyModulus);
        polyModulus.modulus(modulus);
        SmallPolynomialArithmetics.polyPowMod(base.clone(), 100 * modulus, polyModulus, modulus, false);
//        System.out.println(mod(base,polyModulus,modulus));
        if(true) {
            int t = 0;
            for (int i = 0; i < 10000; i++) {
                long start = System.currentTimeMillis();
                t += SmallPolynomialArithmetics.polyPowMod(base.clone(), 100 * modulus, polyModulus, modulus, false).degree;
                System.out.println(System.currentTimeMillis() - start);
            }
            System.out.println(t);
        }
    }
}