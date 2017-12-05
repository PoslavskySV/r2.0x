package cc.redberry.rings.poly;

import cc.redberry.rings.Factors;
import cc.redberry.rings.poly.univar.*;
import org.apache.commons.math3.random.RandomGenerator;

/**
 * Ring of univariate polynomials.
 *
 * @param <Poly> type of univariate polynomials
 * @since 1.0
 */
public final class UnivariateRing<Poly extends IUnivariatePolynomial<Poly>> extends APolynomialRing<Poly> {
    private static final long serialVersionUID = 1L;

    /**
     * Creates ring of univariate polynomials which support operations over univariate polynomials of the type same as
     * of provided {@code factory} polynomial
     *
     * @param factory factory polynomial (the exact value of {@code factory} is irrelevant)
     */
    public UnivariateRing(Poly factory) { super(factory); }

    @Override
    public int nVariables() { return 1; }

    @Override
    public Poly remainder(Poly a, Poly b) {return UnivariateDivision.remainder(a, b, true);}

    @Override
    public Poly[] divideAndRemainder(Poly a, Poly b) {return UnivariateDivision.divideAndRemainder(a, b, true);}

    @Override
    public Poly gcd(Poly a, Poly b) {return UnivariateGCD.PolynomialGCD(a, b);}

    @Override
    public Poly[] extendedGCD(Poly a, Poly b) {
        return UnivariateGCD.PolynomialExtendedGCD(a, b);
    }

    @Override
    public FactorDecomposition<Poly> factorSquareFree(Poly element) {
        return UnivariateSquareFreeFactorization.SquareFreeFactorization(element);
    }

    @Override
    public FactorDecomposition<Poly> factor(Poly element) {
        return UnivariateFactorization.Factor(element);
    }

    @Override
    public Poly variable(int variable) {
        if (variable != 0)
            throw new IllegalArgumentException();
        return factory.createMonomial(1);
    }

    /**
     * Gives a random univariate polynomial with the degree randomly picked from {@code minDegree} (inclusive) to {@code
     * maxDegree} (exclusive)
     *
     * @param minDegree the minimal degree of the result
     * @param maxDegree the maximal degree of the result
     * @param rnd       the source of randomness
     * @return random univariate polynomial with the degree randomly picked from {@code minDegree} (inclusive) to {@code
     * maxDegree} (exclusive)
     * @see RandomUnivariatePolynomials
     */
    public Poly randomElement(int minDegree, int maxDegree, RandomGenerator rnd) {
        return RandomUnivariatePolynomials.randomPoly(factory, minDegree +
                (minDegree == maxDegree ? 0 : rnd.nextInt(maxDegree - minDegree)), rnd);
    }

    /**
     * Gives a random univariate polynomial with the specified degree
     *
     * @param degree the degree of the result
     * @param rnd    the source of randomness
     * @return random univariate polynomial with the specified degree
     */
    public Poly randomElement(int degree, RandomGenerator rnd) {
        return randomElement(degree, degree, rnd);
    }

    /**
     * The minimal degree of polynomial generated with {@link #randomElement(RandomGenerator)}
     */
    public static final int MIN_DEGREE_OF_RANDOM_POLY = 0;
    /**
     * The maximal degree of polynomial generated with {@link #randomElement(RandomGenerator)}
     */
    public static final int MAX_DEGREE_OF_RANDOM_POLY = 32;

    /**
     * Gives a random univariate polynomial with the degree randomly picked from {@link #MIN_DEGREE_OF_RANDOM_POLY}
     * (inclusive) to {@link #MAX_DEGREE_OF_RANDOM_POLY} (exclusive)
     *
     * @param rnd the source of randomness
     * @return random univariate polynomial
     */
    @Override
    public Poly randomElement(RandomGenerator rnd) {
        return randomElement(MIN_DEGREE_OF_RANDOM_POLY, MAX_DEGREE_OF_RANDOM_POLY, rnd);
    }
}
