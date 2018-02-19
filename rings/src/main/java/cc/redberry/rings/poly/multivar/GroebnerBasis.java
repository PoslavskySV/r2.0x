package cc.redberry.rings.poly.multivar;

import cc.redberry.rings.*;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.bigint.BigIntegerUtil;
import cc.redberry.rings.linear.LinearSolver;
import cc.redberry.rings.linear.LinearSolver.SystemInfo;
import cc.redberry.rings.poly.MultivariateRing;
import cc.redberry.rings.poly.UnivariateRing;
import cc.redberry.rings.poly.Util;
import cc.redberry.rings.poly.univar.UnivariateDivision;
import cc.redberry.rings.poly.univar.UnivariatePolynomial;
import cc.redberry.rings.poly.univar.UnivariatePolynomialArithmetic;
import cc.redberry.rings.primes.PrimesIterator;
import cc.redberry.rings.util.ArraysUtil;
import cc.redberry.rings.util.TimeUnits;
import gnu.trove.impl.Constants;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.list.array.TLongArrayList;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.set.hash.TIntHashSet;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;
import java.util.function.ToIntFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static cc.redberry.rings.Rings.*;
import static cc.redberry.rings.linear.LinearSolver.SystemInfo.*;

/**
 * Groebner basis computation.
 *
 * @since 1.0
 */
public final class GroebnerBasis {
    private GroebnerBasis() {}

    /**
     * Computes Groebner basis (minimized and reduced) of a given ideal represented as a list of generators.
     *
     * @param generators    generators of the ideal
     * @param monomialOrder monomial order
     * @return Groebner basis
     */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> GroebnerBasis(List<Poly> generators,
                             Comparator<DegreeVector> monomialOrder) {
        return BuchbergerGB(generators, monomialOrder);
    }

    /* **************************************** Common methods ************************************************ */

    /** Set monomial order inplace */
    @SuppressWarnings("unchecked")
    static <Poly extends AMultivariatePolynomial<?, Poly>>
    void setMonomialOrder(List<Poly> list, Comparator<DegreeVector> order) {
        for (int i = 0; i < list.size(); i++) {
            Poly p = list.get(i);
            if (!order.equals(p.ordering))
                list.set(i, p.setOrdering(order));
        }
    }

    /** Make each poly monic and sort list */
    static <Poly extends AMultivariatePolynomial<?, Poly>>
    List<Poly> canonicalize(List<Poly> list) {
        if (Util.isOverRationals(list.get(0)))
            canonicalizeFrac((List) list);
        else
            list.forEach(Poly::canonical);
        list.sort(Comparable::compareTo);
        return list;
    }

    @SuppressWarnings("unchecked")
    static <E> void canonicalizeFrac(List<MultivariatePolynomial<Rational<E>>> list) {
        Ring<E> fRing = list.get(0).ring.getOne().ring;
        list.replaceAll(p -> Util.toCommonDenominator(p)._1.canonical().mapCoefficients(p.ring, c -> new Rational<>(fRing, c)));
    }

    /** set monomial order, monicize, sort etc. */
    private static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> prepareGenerators(List<Poly> generators, Comparator<DegreeVector> monomialOrder) {
        // clone generators & set monomial order
        generators = generators.stream()
                .map(p -> p.setOrdering(monomialOrder))
                .map(Poly::canonical) // <- make poly monic or primitive
                .collect(Collectors.toList());

        Poly factory = generators.get(0);
        if (factory.nVariables == 1)
            // univariate case
            return canonicalize(Collections.singletonList(MultivariateGCD.PolynomialGCD(generators)));

        // remove zeroes
        generators.removeIf(Poly::isZero);
        if (generators.isEmpty()) {
            // empty ideal
            generators.add(factory.createZero());
            return generators;
        }

        // remove redundant elements from the basis
        removeRedundant(generators);

        // remove zeroes (may occur after reduction)
        generators.removeIf(Poly::isZero);
        if (generators.isEmpty()) {
            // empty ideal
            generators.add(factory.createZero());
            return generators;
        }

        if (generators.stream().anyMatch(Poly::isConstant))
            // contains non zero constant => ideal == whole ring
            return Collections.singletonList(factory.createOne());

        return generators;
    }


    /** Minimizes Groebner basis. The input should be a Groebner basis */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    void minimizeGroebnerBases(List<Poly> basis) {
        outer:
        for (int i = basis.size() - 1; i >= 1; --i) {
            for (int j = i - 1; j >= 0; --j) {
                Poly pi = basis.get(i), pj = basis.get(j);
                if (pi.lt().dvDivisibleBy(pj.lt())) {
                    basis.remove(i);
                    continue outer;
                }
                if (pj.lt().dvDivisibleBy(pi.lt())) {
                    basis.remove(j);
                    --i;
                    continue;
                }
            }
        }
    }

    /** Computes reduced Groebner basis */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    void removeRedundant(List<Poly> basis) {
        for (int i = 0, size = basis.size(); i < size; ++i) {
            Poly el = basis.remove(i);
            Poly r = MultivariateDivision.pseudoRemainder(el, basis);
            if (r.isZero()) {
                --i;
                --size;
            } else
                basis.add(i, r);
        }
    }

    /** Abstract critical pair: used with different Poly type for Buchberger and F4 algorithms */
    public static class SyzygyPair<Term extends AMonomial<Term>, Poly extends MonomialSetView<Term>> {
        /** Positions of polynomials {@code fi} and {@code fj} in the list of generators */
        final int i, j;
        /** Polynomials to form a syzygy */
        final Poly fi, fj;
        /** {@code lcm(fi.lt(), fj.lt())} */
        final DegreeVector syzygyGamma;
        /** The sugar */
        final int sugar;

        SyzygyPair(int i, int j, Poly fi, Poly fj) {
            if (i > j) {
                int s = i; i = j; j = s;
                Poly fs = fi; fi = fj; fj = fs;
            }
            assert i != j && fi != fj;
            assert shareVariablesQ(fi.lt(), fj.lt());
            this.i = i; this.j = j;
            this.fi = fi; this.fj = fj;
            this.syzygyGamma = lcm(fi.lt(), fj.lt());
            this.sugar = Math.max(
                    fi.degreeSum() - fi.lt().totalDegree,
                    fj.degreeSum() - fj.lt().totalDegree) + syzygyGamma.totalDegree;
        }

        SyzygyPair(int i, int j, List<Poly> generators) {
            this(i, j, generators.get(i), generators.get(j));
        }

        /** syzygy degree */
        final int degree() { return syzygyGamma.totalDegree;}

        final int sugar() { return sugar; }
    }

    /** Computes syzygy of given polynomials */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    Poly syzygy(Poly a, Poly b) {
        return syzygy(new DegreeVector(lcm(a.multidegree(), b.multidegree())), a, b);
    }

    /** Computes syzygy of given polynomials */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    Poly syzygy(SyzygyPair<Term, Poly> sPair) {
        return syzygy(sPair.syzygyGamma, sPair.fi, sPair.fj);
    }

    /** Computes syzygy of given polynomials */
    @SuppressWarnings("unchecked")
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    Poly syzygy(DegreeVector dvlcm, Poly a, Poly b) {
        IMonomialAlgebra<Term> mAlgebra = a.monomialAlgebra;
        Term lcm;
        if (a.isOverField())
            lcm = mAlgebra.create(dvlcm);
        else
            lcm = (Term) new Monomial<>(dvlcm,
                    ((MultivariatePolynomial) a).ring.lcm(
                            ((MultivariatePolynomial) a).lc(),
                            ((MultivariatePolynomial) b).lc()));
        Poly
                aReduced = a.clone().multiply(mAlgebra.divideExact(lcm, a.lt())),
                bReduced = b.clone().multiply(mAlgebra.divideExact(lcm, b.lt())),
                syzygy = aReduced.subtract(bReduced);
        return syzygy;
    }

    /**
     * Data structure which holds current set of critical pairs. This set may be just a Set&lt;SyzygyPair&gt; (TreeSet
     * actually), or some more complicated structure (map of sets, e.g. TreeMap&lt;Integer,
     * TreeSet&lt;SyzygyPair&lt;Term, Poly&gt;&gt;&gt; of degree -&gt; set of pairs with this degree) for graded
     * algorithms (F4, homogeneous Buchberger etc).
     */
    interface SyzygySet<Term extends AMonomial<Term>, Poly extends MonomialSetView<Term>> {
        /** add new syzygy to set */
        void add(SyzygyPair<Term, Poly> sPair);

        /** remove syzygy from set */
        void remove(SyzygyPair<Term, Poly> sPair);

        /** is empty */
        boolean isEmpty();

        /** remove a bunch of syzygies to process */
        Collection<SyzygyPair<Term, Poly>> getAndRemoveNextBunch();

        /** a view of all sets of syzygies */
        Collection<TreeSet<SyzygyPair<Term, Poly>>> allSets();

        default List<SyzygyPair<Term, Poly>> allPairs() {
            return allSets().stream().flatMap(Collection::stream).collect(Collectors.toList());
        }
    }

    /**
     * A plain set of critical pairs --- wrapper around TreeSet&lt;SyzygyPair&lt;Term, Poly&gt;&gt;. Elements are
     * ordered according to the comparator of TreeSet instance.
     */
    static final class SyzygyTreeSet<Term extends AMonomial<Term>, Poly extends MonomialSetView<Term>>
            implements SyzygySet<Term, Poly> {
        final TreeSet<SyzygyPair<Term, Poly>> sPairs;

        SyzygyTreeSet(TreeSet<SyzygyPair<Term, Poly>> sPairs) { this.sPairs = sPairs; }

        @Override
        public void add(SyzygyPair<Term, Poly> sPair) { sPairs.add(sPair); }

        @Override
        public void remove(SyzygyPair<Term, Poly> sPair) { sPairs.remove(sPair); }

        @Override
        public boolean isEmpty() { return sPairs.isEmpty(); }

        /**
         * Returns the single element from the top of TreeSet
         */
        @Override
        public Collection<SyzygyPair<Term, Poly>> getAndRemoveNextBunch() {return Collections.singleton(sPairs.pollFirst());}

        /**
         * Returns the single TreeSet (this)
         */
        @Override
        public Collection<TreeSet<SyzygyPair<Term, Poly>>> allSets() { return new ArrayList<>(Collections.singleton(sPairs));}
    }

    /**
     * Graded set of syzygies: critical pairs are collected in the sets each one containing critical pairs with the same
     * degree. Wrapper around TreeMap&lt;Integer, TreeSet&lt;SyzygyPair&lt;Term, Poly&gt;&gt;&gt;
     */
    static final class GradedSyzygyTreeSet<Term extends AMonomial<Term>, Poly extends MonomialSetView<Term>>
            implements SyzygySet<Term, Poly> {
        final TreeMap<Integer, TreeSet<SyzygyPair<Term, Poly>>> sPairs;
        final Comparator<SyzygyPair> selectionStrategy;
        final ToIntFunction<SyzygyPair<Term, Poly>> weightFunction;

        GradedSyzygyTreeSet(TreeMap<Integer, TreeSet<SyzygyPair<Term, Poly>>> sPairs,
                            Comparator<SyzygyPair> selectionStrategy,
                            ToIntFunction<SyzygyPair<Term, Poly>> weightFunction) {
            this.sPairs = sPairs;
            this.selectionStrategy = selectionStrategy;
            this.weightFunction = weightFunction;
        }

        @Override
        public void add(SyzygyPair<Term, Poly> sPair) {
            sPairs.computeIfAbsent(weightFunction.applyAsInt(sPair), __ -> new TreeSet<>(selectionStrategy)).add(sPair);
        }

        @Override
        public void remove(SyzygyPair<Term, Poly> sPair) {
            int weight = weightFunction.applyAsInt(sPair);
            TreeSet<SyzygyPair<Term, Poly>> set = sPairs.get(weight);
            if (set != null) {
                set.remove(sPair);
                if (set.isEmpty())
                    sPairs.remove(weight);
            }
        }

        @Override
        public boolean isEmpty() { return sPairs.isEmpty(); }

        /**
         * Returns all syzygies with the minimal degree
         */
        @Override
        public Collection<SyzygyPair<Term, Poly>> getAndRemoveNextBunch() {return sPairs.pollFirstEntry().getValue();}

        /**
         * Returns sets of syzygies each one with fixed degree
         */
        @Override
        public Collection<TreeSet<SyzygyPair<Term, Poly>>> allSets() { return sPairs.values();}
    }

    /**
     * Generic Buchberger criteria via Gebauer-Moller installation. Algorithm from page 230 of Becker & Weispfenning,
     * 1993. Note: redundant generators in the {@code basis} are marked as null.
     */
    private static <Term extends AMonomial<Term>, Poly extends MonomialSetView<Term>>
    void updateBasis(List<Poly> basis,
                     SyzygySet<Term, Poly> sPairs,
                     Poly newElement) {
        assert !newElement.collection().isEmpty();

        // array of lcm( lt(fi), lt(newElement) ) <- cache once for performance
        int[][] lcm = new int[basis.size()][];

        Term newLeadTerm = newElement.lt();
        for (int i = 0; i < basis.size(); i++) {
            Poly fi = basis.get(i);
            if (fi == null)
                continue;
            lcm[i] = lcm(fi.lt().exponents, newLeadTerm.exponents);
        }

        // first indices of new critical pairs to add
        TIntArrayList pairsToAdd = new TIntArrayList();
        // find new critical pairs that should be definitely added
        filter:
        for (int iIndex = 0; iIndex < basis.size(); ++iIndex) {
            Poly fi = basis.get(iIndex);
            if (fi == null)
                continue;
            if (!shareVariablesQ(fi.lt(), newLeadTerm)) {
                pairsToAdd.add(iIndex); // add disjoint elements (will be removed in the next step)
                continue;
            }

            // ruling out redundant Buchberger triplets: 1st pass
            for (int i = 0; i < pairsToAdd.size(); i++) {
                int jIndex = pairsToAdd.get(i);
                Poly fj = basis.get(jIndex);
                assert fj != null;
                if (dividesQ(lcm[jIndex], lcm[iIndex]))
                    continue filter;
            }

            // ruling out redundant Buchberger triplets: 2st pass
            for (int jIndex = iIndex + 1; jIndex < basis.size(); ++jIndex) {
                Poly fj = basis.get(jIndex);
                if (fj == null)
                    continue;
                if (dividesQ(lcm[jIndex], lcm[iIndex]))
                    continue filter;
            }

            // no any redundant Buchberger triplets found -> add new critical pair
            pairsToAdd.add(iIndex);
        }

        // now rule out disjoint elements
        for (int i = pairsToAdd.size() - 1; i >= 0; --i)
            if (!shareVariablesQ(basis.get(pairsToAdd.get(i)).lt(), newLeadTerm))
                pairsToAdd.removeAt(i);

        // ruling out redundant Buchberger triplets from the old set of critical pairs
        Iterator<TreeSet<SyzygyPair<Term, Poly>>> it = sPairs.allSets().iterator();
        while (it.hasNext()) {
            TreeSet<SyzygyPair<Term, Poly>> c = it.next();
            // remove redundant critical pairs
            c.removeIf(sPair -> dividesQ(newLeadTerm, sPair.syzygyGamma)
                    && !Arrays.equals(sPair.fi == basis.get(sPair.i) ? lcm[sPair.i] : lcm(sPair.fi.lt().exponents, newLeadTerm.exponents), sPair.syzygyGamma.exponents)
                    && !Arrays.equals(sPair.fj == basis.get(sPair.j) ? lcm[sPair.j] : lcm(sPair.fj.lt().exponents, newLeadTerm.exponents), sPair.syzygyGamma.exponents));
            if (c.isEmpty())
                it.remove();
        }

        // now add new element to the basis
        int oldSize = basis.size();
        basis.add(newElement);

        // update set of critical pairs with pairsToAdd
        for (int i = 0; i < pairsToAdd.size(); ++i) {
            int iIndex = pairsToAdd.get(i);
            assert basis.get(iIndex) != null;
            sPairs.add(new SyzygyPair<>(iIndex, oldSize, basis));
        }


//        The following simplification is removed, since it is valid only when lead reduction is used
//        (we use full reduction everywhere)
//
//        // remove old basis elements that are now redundant
//        // note: do that only after update of critical pair set
//        // note: this is compatible only with LeadReduce function,
//        // in other cases one should keep track of all reducers
//        // so this will only help to eliminate Buchberger triplets faster
//        for (int iIndex = 0; iIndex < oldSize; ++iIndex) {
//            Poly fi = basis.get(iIndex);
//            if (fi == null)
//                continue;
//            if (dividesQ(newLeadTerm, fi.lt()))
//                basis.set(iIndex, null);
//        }
    }

    /**
     * Check whether specified generators form Groebner basis of given ideal
     */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    boolean isGroebnerBasis(List<Poly> ideal, List<Poly> generators, Comparator<DegreeVector> monomialOrder) {
        // form set of syzygies to check
        SyzygySet<Term, Poly> sPairs = new SyzygyTreeSet<>(new TreeSet<>(defaultSelectionStrategy(monomialOrder)));
        List<Poly> tmp = new ArrayList<>();
        ideal.forEach(g -> updateBasis(tmp, sPairs, g));

        Poly factory = ideal.get(0);
        Poly[] gb = generators.toArray(factory.createArray(generators.size()));
        return sPairs.allSets().stream().flatMap(Collection::stream)
                .allMatch(p -> MultivariateDivision.pseudoRemainder(syzygy(p), gb).isZero());
    }

    /**
     * Normal selection strategy: chose syzygy with the less lcm(fi.lt(), fj.lt()) with respect to monomialOrder
     */
    public static Comparator<SyzygyPair> normalSelectionStrategy(Comparator<DegreeVector> monomialOrder) {
        return (sa, sb) -> {
            int c = monomialOrder.compare(sa.syzygyGamma, sb.syzygyGamma);
            if (c != 0)
                return c;
            c = Integer.compare(sa.j, sb.j);
            if (c != 0)
                return c;
            return Integer.compare(sa.i, sb.i);
        };
    }

    /**
     * Add sugar to selection strategy: pick syzygy with less sugar first, break tie with the initial strategy
     */
    public static Comparator<SyzygyPair> withSugar(Comparator<SyzygyPair> initial) {
        return (sa, sb) -> {
            int c = Integer.compare(sa.sugar, sb.sugar);
            if (c != 0)
                return c;
            return initial.compare(sa, sb);
        };
    }

    /**
     * Default selection strategy (with or without sugar)
     */
    public static Comparator<SyzygyPair> defaultSelectionStrategy(Comparator<DegreeVector> monomialOrder) {
        Comparator<SyzygyPair> selectionStrategy = normalSelectionStrategy(monomialOrder);
        // fixme use sugar always?
        if (!isGradedOrder(monomialOrder))
            // add sugar for non-graded orders
            selectionStrategy = withSugar(selectionStrategy);
        return selectionStrategy;
    }

    /** Ecart comparator */
    private static final class EcartComparator<Poly extends AMultivariatePolynomial<?, Poly>>
            implements Comparator<Poly> {
        @Override
        public int compare(Poly a, Poly b) {
            int c = Integer.compare(a.ecart(), b.ecart());
            if (c != 0)
                return c;
            return a.ordering.compare(a.lt(), b.lt());
        }
    }

    /** whether monomial order is graded */
    static boolean isGradedOrder(Comparator<DegreeVector> monomialOrder) {
        return monomialOrder == MonomialOrder.GREVLEX || monomialOrder == MonomialOrder.GRLEX;
    }

    /** l.c.m. of degree vectors */
    static DegreeVector lcm(DegreeVector a, DegreeVector b) {
        return new DegreeVector(lcm(a.exponents, b.exponents));
    }

    /** l.c.m. of degree vectors */
    static int[] lcm(int[] a, int[] b) {
        return ArraysUtil.max(a, b);
    }

    /** whether dividend degree vector can be divided by divider degree vector */
    private static boolean dividesQ(int[] divider, int[] dividend) {
        for (int i = 0; i < dividend.length; i++)
            if (dividend[i] < divider[i])
                return false;
        return true;
    }

    /** whether dividend monomial can be divided by divider monomial */
    private static boolean dividesQ(DegreeVector divider, DegreeVector dividend) {
        return dividend.dvDivisibleBy(divider);
    }

    /** have variables in common */
    static boolean shareVariablesQ(DegreeVector a, DegreeVector b) {
        for (int i = 0; i < a.exponents.length; i++)
            if (a.exponents[i] != 0 && b.exponents[i] != 0)
                return true;
        return false;
    }

    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> homogenize(List<Poly> ideal) {
        return ideal.stream().map(p -> p.homogenize(p.nVariables)).collect(Collectors.toList());
    }

    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> dehomogenize(List<Poly> ideal) {
        return ideal.stream().map(p -> p.dropVariable(p.nVariables - 1)).collect(Collectors.toList());
    }

    static <E> List<MultivariatePolynomial<E>> toIntegral(List<MultivariatePolynomial<Rational<E>>> ideal) {
        return ideal.stream()
                .map(p -> Util.toCommonDenominator(p)._1)
                .collect(Collectors.toList());
    }

    static <E> List<MultivariatePolynomial<Rational<E>>> toFractions(List<MultivariatePolynomial<E>> ideal) {
        Ring<Rational<E>> ring = Frac(ideal.get(0).ring);
        return ideal.stream()
                .map(p -> p.mapCoefficients(ring, c -> new Rational<>(p.ring, c)))
                .collect(Collectors.toList());
    }

    /** Groebner basis over fraction fields */
    static <E> List<MultivariatePolynomial<Rational<E>>>
    FracGB(List<MultivariatePolynomial<Rational<E>>> ideal,
           Comparator<DegreeVector> monomialOrder,
           GroebnerAlgorithm<Monomial<E>, MultivariatePolynomial<E>> algorithm) {
        return toFractions(algorithm.GroebnerBasis(toIntegral(ideal), monomialOrder));
    }

    interface GroebnerAlgorithm<
            Term extends AMonomial<Term>,
            Poly extends AMultivariatePolynomial<Term, Poly>> {
        List<Poly> GroebnerBasis(List<Poly> ideal, Comparator<DegreeVector> monomialOrder);
    }

    /* ************************************** Buchberger algorithm ********************************************** */

    /**
     * Computes minimized and reduced Groebner basis of a given ideal via Buchberger algorithm. It uses normal strategy
     * for graded orders and sugar strategy for lexicographic.
     */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> BuchbergerGB(List<Poly> ideal, Comparator<DegreeVector> monomialOrder) {
        return BuchbergerGB(ideal, monomialOrder, defaultSelectionStrategy(monomialOrder), NO_MINIMIZATION);
    }

    /**
     * Computes minimized and reduced Groebner basis of a given ideal via Buchberger algorithm.
     *
     * @param generators           generators of the ideal
     * @param monomialOrder        monomial order to use
     * @param selectionStrategy    critical pair selection strategy
     * @param minimizationStrategy how to minimize Groebner basis at intermediate steps
     */
    @SuppressWarnings("unchecked")
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> BuchbergerGB(List<Poly> generators,
                            Comparator<DegreeVector> monomialOrder,
                            Comparator<SyzygyPair> selectionStrategy,
                            MinimizationStrategy minimizationStrategy) {
        if (Util.isOverRationals(generators.get(0)))
            return (List<Poly>) FracGB((List) generators, monomialOrder, GroebnerBasis::BuchbergerGB);

        return BuchbergerGB(generators, monomialOrder, minimizationStrategy,
                () -> new SyzygyTreeSet<>(new TreeSet<>(selectionStrategy)));
    }

    /**
     * Computes minimized and reduced Groebner basis of a given homogeneous ideal via Buchberger algorithm.
     */
    @SuppressWarnings("unchecked")
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> BuchbergerHomogeneousGB(List<Poly> generators,
                                       Comparator<DegreeVector> monomialOrder) {
        if (Util.isOverRationals(generators.get(0)))
            return (List<Poly>) FracGB((List) generators, monomialOrder, GroebnerBasis::BuchbergerHomogeneousGB);

        Comparator<SyzygyPair> selectionStrategy = normalSelectionStrategy(generators.get(0).ordering);
        // fixme use sugar always?
        if (!isGradedOrder(monomialOrder))
            // add sugar for non-graded orders
            selectionStrategy = withSugar(selectionStrategy);
        return BuchbergerHomogeneousGB(generators, monomialOrder, selectionStrategy, NO_MINIMIZATION);
    }

    /**
     * Computes minimized and reduced Groebner basis of a given homogeneous ideal via Buchberger algorithm.
     *
     * @param generators        generators of the ideal
     * @param monomialOrder     monomial order to use
     * @param selectionStrategy critical pair selection strategy
     */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> BuchbergerHomogeneousGB(List<Poly> generators,
                                       Comparator<DegreeVector> monomialOrder,
                                       Comparator<SyzygyPair> selectionStrategy,
                                       MinimizationStrategy minimizationStrategy) {
        return BuchbergerGB(generators, monomialOrder, minimizationStrategy,
                () -> new GradedSyzygyTreeSet<>(new TreeMap<>(), selectionStrategy, SyzygyPair::degree));
    }

    /**
     * Generic implementation of Buchberger algorithm.
     *
     * @param generators           generators of the ideal
     * @param monomialOrder        monomial order to use
     * @param minimizationStrategy minimization strategy
     * @param syzygySetSupplier    supplies data structure for managing syzygies
     */
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> BuchbergerGB(List<Poly> generators,
                            Comparator<DegreeVector> monomialOrder,
                            MinimizationStrategy minimizationStrategy,
                            Supplier<SyzygySet<Term, Poly>> syzygySetSupplier) {
        // simplify generators as much as possible
        generators = prepareGenerators(generators, monomialOrder);
        if (generators.size() == 1)
            return generators;

        Poly factory = generators.get(0);

        // sort polynomials in the basis to achieve faster divisions
        Comparator<Poly> polyOrder = isGradedOrder(monomialOrder)
                ? (a, b) -> monomialOrder.compare(a.lt(), b.lt())
                : new EcartComparator<>();
        generators.sort(polyOrder);

        // set of syzygies
        SyzygySet<Term, Poly> sPairs = syzygySetSupplier.get();

        // Groebner basis that will be computed
        List<Poly> groebner = new ArrayList<>();
        // update Groebner basis with initial generators
        generators.forEach(g -> updateBasis(groebner, sPairs, g));
        // cache array used in divisions (little performance improvement actually)
        Poly[] reducersArray = groebner.stream().filter(Objects::nonNull).toArray(factory::createArray);

        // cache size of basis after each minimization
        int sizeAfterMinimization = groebner.size();
        while (!sPairs.isEmpty())
            // pick up (and remove) a bunch of critical pairs
            for (SyzygyPair<Term, Poly> pair : sPairs.getAndRemoveNextBunch()) {
                // compute actual syzygy
                Poly syzygy = MultivariateDivision.pseudoRemainder(syzygy(pair), reducersArray);
                if (syzygy.isZero())
                    continue;

                if (syzygy.isConstant())
                    // ideal = ring
                    return Collections.singletonList(factory.createOne());

                // add syzygy to basis
                updateBasis(groebner, sPairs, syzygy);
                // recompute array
                reducersArray = groebner.stream().filter(Objects::nonNull).toArray(factory::createArray);
                // don't sort here, not practical actually
                // Arrays.sort(groebnerArray, polyOrder);

                if (minimizationStrategy.doMinimize(sizeAfterMinimization, groebner.size())) {
                    reduceAndMinimizeGroebnerBases(groebner, sPairs, sizeAfterMinimization);
                    sizeAfterMinimization = groebner.size();
                }
            }

        // batch remove all nulls
        groebner.removeAll(Collections.<Poly>singleton(null));
        // minimize Groebner basis
        minimizeGroebnerBases(groebner);
        // speed up final reduction
        groebner.sort(polyOrder);
        // reduce Groebner basis
        removeRedundant(groebner);
        // canonicalize Groebner basis
        canonicalize(groebner);

        return groebner;
    }

    /** Strategy used to reduce and minimize basis in the intermediate steps of Buchberger algorithm */
    public interface MinimizationStrategy {
        /**
         * true means "yes, do minimization and reduction", false means "just keep all generators as is"
         *
         * @param previousSize size of generators list on the previous invocation of minimization
         * @param currentSize  current size of generators list
         */
        boolean doMinimize(int previousSize, int currentSize);
    }

    /** no any minimization at intermediate steps, just keep all track of generators as is */
    public static MinimizationStrategy NO_MINIMIZATION = (prev, curr) -> false;

    /** reduce & minimize current basis */
    private static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    void reduceAndMinimizeGroebnerBases(List<Poly> generators,
                                        SyzygySet<Term, Poly> sPairs,
                                        int from) {
        for (int i = from; i < generators.size(); i++) {
            // this are newly added elements of Groebner basis
            Poly fi = generators.get(i);
            if (fi == null)
                continue;

            for (int j = 0; j < i; ++j) { // search for fj which is divisible by fi
                Poly fj = generators.get(j);
                if (fj == null)
                    continue;

                // proceed only if new syzygy can reduce fk
                if (!MultivariateDivision.nontrivialQuotientQ(fj, fi))
                    continue;

                generators.remove(j);
                Poly reduced = remainder0(fj, generators);
                if (reduced.equals(fj))
                    continue;

                if (reduced.isZero()) // remove element
                    reduced = null;

                generators.add(j, reduced);

                if (!fj.equals(reduced)) {
                    if (reduced == null) {
                        // remove all pairs with k
                        for (int l = 0; l < generators.size(); l++)
                            if (l != j && generators.get(l) != null)
                                sPairs.remove(new SyzygyPair<>(l, j, generators));
                    } else
                        // update all pairs with k
                        for (int l = 0; l < generators.size(); l++)
                            if (l != j && generators.get(l) != null)
                                sPairs.add(new SyzygyPair<>(l, j, generators));
                }
            }
        }
    }

    private static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    Poly remainder0(Poly dividend, List<Poly> dividers) {
        Poly[] dividersArr = dividers.stream().filter(Objects::nonNull).toArray(dividend::createArray);
        //Arrays.sort(dividersArr, (a, b) -> a.ordering.compare(a.lt(), b.lt()));
        return MultivariateDivision.pseudoRemainder(dividend, dividersArr);
    }

    /* ************************************************** F4 ******************************************************* */

    /**
     * Computes minimized and reduced Groebner basis of a given ideal via F4 algorithm.
     *
     * @param generators    generators of the ideal
     * @param monomialOrder monomial order to use
     */
    @SuppressWarnings("unchecked")
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> F4GB(List<Poly> generators,
                    Comparator<DegreeVector> monomialOrder) {
        if (!isGradedOrder(monomialOrder))
            throw new UnsupportedOperationException("F4 works only with graded orders");
        if (Util.isOverRationals(generators.get(0)))
            return (List<Poly>) FracGB((List) generators, monomialOrder, GroebnerBasis::F4GB);

        return F4GB(generators, monomialOrder,
                () -> new GradedSyzygyTreeSet<>(new TreeMap<>(), defaultSelectionStrategy(monomialOrder), SyzygyPair::degree));
    }

    /*
     * In F4 algorithm we don't need tree-based structure for multivariate polynomials, since no any additions/divisions
     * performed (all operations are reduced to matrix operations). The only arithmetic operation used under the hood
     * of F4 is multiplication by monomial, which still preserves the order of terms. So, we switch here to array-based
     * (with sorted array) representation of polynomials which is much faster than tree-based.
     */

    /**
     * Array-based polynomial representation. The data array is sorted in descending order, so the first element is the
     * leading term.
     */
    private static final class ArrayBasedPoly<Term extends AMonomial<Term>> implements MonomialSetView<Term> {
        /** sorted (in reverse order, so lt is the first) array of terms */
        final IMonomialAlgebra<Term> mAlgebra;
        final Term[] data;
        final int[] degrees;

        ArrayBasedPoly(AMultivariatePolynomial<Term, ?> poly) {
            // retrieve data array from poly in descending order
            this.mAlgebra = poly.monomialAlgebra;
            this.data = poly.terms.descendingMap().values().toArray(poly.monomialAlgebra.createArray(poly.size()));
            this.degrees = poly.degrees();
        }

        ArrayBasedPoly(IMonomialAlgebra<Term> mAlgebra, Term[] data, int[] degrees) {
            this.mAlgebra = mAlgebra;
            this.data = data;
            this.degrees = degrees;
        }

        ArrayBasedPoly(IMonomialAlgebra<Term> mAlgebra, Term[] data, int nVariables) {
            this.mAlgebra = mAlgebra;
            this.data = data;
            this.degrees = new int[nVariables];
            for (Term db : data)
                for (int i = 0; i < nVariables; i++)
                    if (db.exponents[i] > degrees[i])
                        degrees[i] = db.exponents[i];
        }

        @Override
        public Iterator<Term> ascendingIterator() { throw new UnsupportedOperationException(); }

        @Override
        public Iterator<Term> descendingIterator() { return Arrays.asList(data).iterator(); }

        @Override
        public Iterator<Term> iterator() { return descendingIterator(); }

        @Override
        public int[] degrees() { return degrees; }

        @Override
        public Term first() { return data[data.length - 1]; }

        @Override
        public Term last() { return data[0]; }

        int size() { return data.length; }

        Term get(int i) { return data[i]; }

        Term find(Term dv, Comparator<DegreeVector> ordering) {
            int i = Arrays.binarySearch(data, dv, (a, b) -> ordering.compare(b, a));
            if (i < 0)
                return null;
            return data[i];
        }

        @Override
        public Collection<Term> collection() { return Arrays.asList(data); }

        @Override
        public ArrayBasedPoly<Term> clone() { return new ArrayBasedPoly<>(mAlgebra, data.clone(), degrees.clone()); }

        @Override
        public String toString() {
            return Arrays.toString(data);
        }

        void multiply(Term term) {
            for (int i = data.length - 1; i >= 0; --i)
                data[i] = mAlgebra.multiply(data[i], term);
            for (int i = 0; i < degrees.length; ++i)
                degrees[i] += term.exponents[i];
        }

        void multiply(DegreeVector term) {
            for (int i = data.length - 1; i >= 0; --i)
                data[i] = data[i].multiply(term);
            for (int i = 0; i < degrees.length; ++i)
                degrees[i] += term.exponents[i];
        }

        void divideExact(Term term) {
            for (int i = data.length - 1; i >= 0; --i)
                data[i] = mAlgebra.divideExact(data[i], term);
            for (int i = 0; i < degrees.length; ++i)
                degrees[i] -= term.exponents[i];
        }

        /** Multiply array-based poly by a monomial */
        void monic() {
            Term unit = mAlgebra.getUnitTerm(lt().exponents.length);
            multiply(mAlgebra.divideExact(unit, lt().setDegreeVector(unit)));
        }

        @SuppressWarnings("unchecked")
        void primitivePart() {
            if (mAlgebra instanceof IMonomialAlgebra.MonomialAlgebra) {
                Ring ring = ((IMonomialAlgebra.MonomialAlgebra) mAlgebra).ring;
                Object gcd = ring.gcd(Arrays.stream(data).map(t -> ((Monomial) t).coefficient).collect(Collectors.toList()));
                this.divideExact((Term) new Monomial(data[0].exponents.length, gcd));
            }
        }

        void canonical() {
            if (mAlgebra instanceof IMonomialAlgebra.MonomialAlgebra
                    && !((IMonomialAlgebra.MonomialAlgebra) mAlgebra).ring.isField())
                primitivePart();
            else
                monic();
        }

        /** Sets the leading coefficient of poly from the coefficient of term (poly is copied only if necessary) */
        ArrayBasedPoly<Term> setLeadCoeffFrom(Term term) {
            if (mAlgebra.haveSameCoefficients(lt(), term))
                return this;
            ArrayBasedPoly<Term> poly = clone();
            poly.multiply(mAlgebra.divideExact(term.toZero(), poly.lt().toZero()));
            return poly;
        }
    }

    /** Minimal size of selected set of critical pairs */
    private static final int F4_MIN_SELECTION_SIZE = 0; // not used actually

    /** The boundary size of S-pairs set when still normal Buchberger algorithm should be applied */
    private static final int
            F4_OVER_FIELD_LINALG_THRESHOLD = 16,
            F4_OVER_EUCLID_LINALG_THRESHOLD = 0; // always use linear algebra for polynomials over Euclidean rings

    /**
     * Computes minimized and reduced Groebner basis of a given ideal via Faugère's F4 algorithm.
     *
     * Simplification routine used is due to Joux & Vitse, "A variant of F4 algorithm",
     * https://eprint.iacr.org/2010/158.pdf, 2011
     *
     * @param generators    generators of the ideal
     * @param monomialOrder monomial order to use
     */
    public static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> F4GB(List<Poly> generators,
                    Comparator<DegreeVector> monomialOrder,
                    Supplier<SyzygySet<Term, ArrayBasedPoly<Term>>> syzygySetSupplier) {
        // simplify generators as much as possible
        generators = prepareGenerators(generators, monomialOrder);
        if (generators.size() == 1)
            return canonicalize(generators);

        Poly factory = generators.get(0);

        // sort polynomials in the basis to achieve in general faster inital reductions
        Comparator<Poly> polyOrder = isGradedOrder(monomialOrder)
                ? (a, b) -> monomialOrder.compare(a.lt(), b.lt())
                : new EcartComparator<>();
        generators.sort(polyOrder);

        // set of all syzygies
        SyzygySet<Term, ArrayBasedPoly<Term>> sPairs = syzygySetSupplier.get();
        // Groebner basis that will be computed
        List<ArrayBasedPoly<Term>> groebner = new ArrayList<>();

        // a history of performed reductions: index of generator -> list of available reductions
        // this is extensively used in simplify routine; the data is updated each time when a new row-echelon
        // form is calculated; for details see Joux & Vitse, "A variant of F4 algorithm" (TabSimplify structure)
        List<List<ArrayBasedPoly<Term>>> f4reductions = new ArrayList<>();

        // update Groebner basis with initial generators
        for (Poly generator : generators) {
            ArrayBasedPoly<Term> g = new ArrayBasedPoly<>(generator);
            updateBasis(groebner, sPairs, g);
            f4reductions.add(new ArrayList<>(Collections.singletonList(g)));
        }

        // a list of reducers that will be used for a full  direct (without linear algebra) reduction of syzygies
        List<Poly> reducers = new ArrayList<>(generators);
        // cache array used in divisions (little performance improvement actually)
        Poly[] reducersArray = reducers.stream().filter(Objects::nonNull).toArray(factory::createArray);

        main:
        while (!sPairs.isEmpty()) {
            // pick up and remove a bunch of pairs (select at least F4_MIN_SELECTION_SIZE pairs)
            Collection<SyzygyPair<Term, ArrayBasedPoly<Term>>> subset = sPairs.getAndRemoveNextBunch();
            assert !subset.isEmpty();

            while (!sPairs.isEmpty() && subset.size() < F4_MIN_SELECTION_SIZE)
                subset.addAll(sPairs.getAndRemoveNextBunch());

            if ((factory.isOverField() && subset.size() <= F4_OVER_FIELD_LINALG_THRESHOLD)
                    || (!factory.isOverField() && subset.size() <= F4_OVER_EUCLID_LINALG_THRESHOLD)) {
                // normal Buchberger case, don't use linear algebra, just reduce
                for (SyzygyPair<Term, ArrayBasedPoly<Term>> sPair : subset) {
                    // compute actual syzygy
                    Poly syzygy = syzygy(sPair.syzygyGamma, factory.create(sPair.fi), factory.create(sPair.fj));
                    syzygy = MultivariateDivision.pseudoRemainder(syzygy, reducersArray);
                    if (syzygy.isZero())
                        continue;

                    if (syzygy.isConstant())
                        // ideal = ring
                        return Collections.singletonList(factory.createOne());

                    // add syzygy to basis
                    ArrayBasedPoly<Term> _syzygy_ = new ArrayBasedPoly<>(syzygy);
                    updateBasis(groebner, sPairs, _syzygy_);
                    // update F4 reductions
                    f4reductions.add(new ArrayList<>(Collections.singletonList(_syzygy_)));
                    // add syzygy to a list of reducers
                    reducers.add(syzygy);
                    // recompute array
                    reducersArray = reducers.stream().filter(Objects::nonNull).toArray(factory::createArray);
                }
                continue main;
            }

            // the list of polynomials to reduce (H-polynomials)
            List<HPolynomial<Term>> hPolynomials = new ArrayList<>();
            // all monomials that occur in H-polynomials
            TreeSet<DegreeVector> hMonomials = new TreeSet<>(monomialOrder);
            // monomials that were annihilated
            TreeSet<DegreeVector> hAnnihilated = new TreeSet<>(monomialOrder);

            // form initial set of H-polynomials from the current set of critical pairs
            for (SyzygyPair<Term, ArrayBasedPoly<Term>> syzygy : subset) {
                // correction factors
                DegreeVector
                        fiQuot = syzygy.syzygyGamma.dvDivideExact(syzygy.fi.lt()),
                        fjQuot = syzygy.syzygyGamma.dvDivideExact(syzygy.fj.lt());

                // a pair of H-polynomials
                ArrayBasedPoly<Term>
                        fiHPoly = simplify(syzygy.fi, fiQuot, f4reductions.get(syzygy.i)),
                        fjHPoly = simplify(syzygy.fj, fjQuot, f4reductions.get(syzygy.j));

                assert fiHPoly.lt().dvEquals(fjHPoly.lt()) : fiHPoly.lt() + " " + fjHPoly.lt();

                // add to set of H-polynomials
                hPolynomials.add(new HPolynomial<>(fiHPoly, syzygy.i));
                hPolynomials.add(new HPolynomial<>(fjHPoly, syzygy.j));

                // store all monomials that we have in H
                hMonomials.addAll(fiHPoly.collection());
                hMonomials.addAll(fjHPoly.collection());

                // lts will be annihilated
                hAnnihilated.add(fiHPoly.lt());
            }

            // the diff = Mon(H-polynomials) / annihilated
            TreeSet<DegreeVector> diff = new TreeSet<>(monomialOrder);
            diff.addAll(hMonomials);
            diff.removeAll(hAnnihilated);

            // compute a whole set of required H-polynomials for reductions
            // ("Symbolic Preprocessing" routine from Faugère's original paper)
            while (!diff.isEmpty()) {
                // pick the "highest" term from diff
                DegreeVector dv = diff.pollLast();
                hAnnihilated.add(dv);

                // select some polynomial from basis which can reduce the "highest" term (lt-divisor)
                OptionalInt divisorOpt = IntStream.range(0, groebner.size())
                        .filter(i -> groebner.get(i) != null)
                        .filter(i -> dv.dvDivisibleBy(groebner.get(i).lt()))
                        .findAny();
                if (divisorOpt.isPresent()) {
                    // index in the basis
                    int iIndex = divisorOpt.getAsInt();
                    // correction factor
                    DegreeVector quot = dv.dvDivideExact(groebner.get(iIndex).lt());
                    // new H-polynomial to add
                    ArrayBasedPoly<Term> newH = simplify(groebner.get(iIndex), quot, f4reductions.get(iIndex));

                    // append newH to H-polynomials
                    hPolynomials.add(new HPolynomial<>(newH, iIndex));
                    // update monomials set
                    TreeSet<DegreeVector> newMonomials = new TreeSet<>(monomialOrder);
                    newMonomials.addAll(newH.collection());
                    hMonomials.addAll(newMonomials);

                    // update the diff
                    newMonomials.removeAll(hAnnihilated);
                    diff.addAll(newMonomials);
                }
            }

            // all monomials occurring in H sorted in descending order, i.e. lead term first
            DegreeVector[] hMonomialsArray = hMonomials.descendingSet().toArray(new DegreeVector[hMonomials.size()]);
            // sort rows to make the initial matrix upper-right-triangular as max as possible
            hPolynomials.sort((a, b) -> {
                int c = monomialOrder.compare(b.hPoly.lt(), a.hPoly.lt());
                if (c != 0)
                    return c;
                return Integer.compare(a.hPoly.size(), b.hPoly.size());
            });
            // reduce all H-polynomials with linear algebra and compute new basis elements (N+)
            List<ArrayBasedPoly<Term>> nPlus = reduceMatrix(factory, groebner, hPolynomials, hMonomialsArray, f4reductions);
            // enlarge the basis
            nPlus.forEach(g -> updateBasis(groebner, sPairs, g));
            // add reducers to a list of reducers
            nPlus.forEach(g -> reducers.add(factory.create(g)));
            for (int i = 0; i < groebner.size(); ++i)
                if (groebner.get(i) == null)
                    reducers.set(i, null);

            // recompute array
            reducersArray = reducers.stream().filter(Objects::nonNull).toArray(factory::createArray);
        }
        // batch remove all nulls
        groebner.removeAll(Collections.<ArrayBasedPoly<Term>>singleton(null));

        // convert from array-based polynomials to normal
        List<Poly> result = groebner.stream().map(factory::create).collect(Collectors.toList());
        // minimize Groebner basis
        minimizeGroebnerBases(result);
        // speed up final reduction
        result.sort(polyOrder);
        // reduce Groebner basis
        removeRedundant(result);
        // canonicalize Groebner basis
        canonicalize(result);

        return result;
    }

    /**
     * A simple container for polynomial and the index of this polynomial (or initial basis polynomial which was reduced
     * in F4 to this polynomial) in the list of generators
     */
    static final class HPolynomial<Term extends AMonomial<Term>> {
        /** polynomial */
        final ArrayBasedPoly<Term> hPoly;
        /** index in generators list of the original polynomial */
        final int indexOfOrigin;

        HPolynomial(ArrayBasedPoly<Term> hPoly, int indexOfOrigin) {
            this.hPoly = hPoly;
            this.indexOfOrigin = indexOfOrigin;
        }
    }

    /**
     * Simplifies h-polynomial by replacing it with its previously computed reduction. For details see Joux & Vitse, "A
     * variant of F4 algorithm", https://eprint.iacr.org/2010/158.pdf, 2011
     *
     * @param generator  the generator (H-polynomial to add is a product of factor * generator)
     * @param factor     correction factor for generator (H-polynomial to add is a product of factor * generator)
     * @param reductions a list of previously obtained reductions of the generator
     */
    static <Term extends AMonomial<Term>>
    ArrayBasedPoly<Term> simplify(ArrayBasedPoly<Term> generator,
                                  DegreeVector factor,
                                  List<ArrayBasedPoly<Term>> reductions) {
        // the desired leading term of H-polynomial
        DegreeVector desiredLeadTerm = generator.lt().dvMultiply(factor);

        // iterate from the last (most recently added, thus most simplified) to the first (the initial generator) reductions
        for (int i = reductions.size() - 1; i >= 0; --i) {
            ArrayBasedPoly<Term> reduction = reductions.get(i);
            // leading term of previously computed reduction
            Term rLeadTerm = reduction.lt();

            if (rLeadTerm.dvEquals(desiredLeadTerm))
                // we just have the same calculation in the map (no any appropriate reductions were calculated)
                return reduction;

            if (desiredLeadTerm.dvDivisibleBy(rLeadTerm)) {
                // <- nontrivial appropriate reduction

                DegreeVector quot = desiredLeadTerm.dvDivideExact(rLeadTerm);
                ArrayBasedPoly<Term> g = reduction.clone();
                g.multiply(quot);

                // cache this reduction too
                reductions.add(g);
                return g;
            }
        }

        // <- this point is unreachable since the initial generator is already added to the list (in the begining)
        throw new RuntimeException();
    }

    /**
     * Computes row echelon form of the matrix and returns new elements to add to the basis
     *
     * @param factory      factory polynomials
     * @param basis        the basis computed so far
     * @param hPolynomials list of prepared H-polynomials
     * @param hMonomials   all the monomials occurring in the H-polynomials list (sorted in descending order)
     * @param f4reductions reductions computed previously for all basis elements
     */
    @SuppressWarnings("unchecked")
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<ArrayBasedPoly<Term>> reduceMatrix(Poly factory,
                                            List<ArrayBasedPoly<Term>> basis,
                                            List<HPolynomial<Term>> hPolynomials,
                                            DegreeVector[] hMonomials,
                                            List<List<ArrayBasedPoly<Term>>> f4reductions) {
        if (hPolynomials.isEmpty())
            return new ArrayList<>();

        if (factory instanceof MultivariatePolynomialZp64)
            return (List<ArrayBasedPoly<Term>>) reduceMatrixZp64(
                    (MultivariatePolynomialZp64) factory, (List) basis, (List) hPolynomials, hMonomials, (List) f4reductions);
        else
            return (List<ArrayBasedPoly<Term>>) reduceMatrixE(
                    (MultivariatePolynomial) factory, (List) basis, (List) hPolynomials, hMonomials, (List) f4reductions);
    }

    private static final double DENSE_FILLING_THRESHOLD = 0.1;

    /* ******************************************* F4 Zp64 linear algebra ******************************************* */


    @SuppressWarnings("unchecked")
    private static List<ArrayBasedPoly<MonomialZp64>> reduceMatrixZp64(
            MultivariatePolynomialZp64 factory,
            List<ArrayBasedPoly<MonomialZp64>> basis,
            List<HPolynomial<MonomialZp64>> hPolynomials,
            DegreeVector[] hMonomials,
            List<List<ArrayBasedPoly<MonomialZp64>>> f4reductions) {
        IntegersZp64 ring = factory.ring;
        IMonomialAlgebra<MonomialZp64> mAlgebra = factory.monomialAlgebra;

        // We use the structured Gaussian elimination strategy as described in
        // J.-C. Faugere & S. Lachartre, PASCO'10 https://doi.org/10.1145/1837210.1837225
        // "Parallel Gaussian Elimination for Gröbner bases computations in finite fields"
        //
        // By swapping the rows and non-pivoting columns, each matrix in F4
        // can be rewritten in the following form (F4-form):
        //
        //    \x0x00xx000x | x0x00xx0000x0x0x0xx000xx000xx0
        //    0\x0x0x00xx0 | 0xx0000x0xxx0x00xx0x0000xx0000
        //    00\x00x000x0 | 0x0x0000x0x0xx00xx0x00x0x0xx00
        //    000\xx0x0x00 | xx0xxx00x000x0x0xx00x0x0xx000x
        //    0000\xx0x0x0 | x0000xx0x00x0xxx0xx0000x000xx0
        //    00000\x0000x | 00x0000x0x0x0xx0xx0xx000xx0000
        //    000000\xx00x | 0x0x000x00x0xxx0xx00xxx0x0xx00
        //    0000000\x0x0 | xx00xx00xx00x000xx0xx00x0x000x
        //    ............ | ..............................
        //    -------------+-------------------------------
        //    0xx000x0x0xx | xxxxxx0xxxxxxx0xxxxxxxxxxxxxxx
        //    x0xx000x0x00 | xxxx0xxxxxxxxxxxxxx0xxxxxxxxxx
        //    00x00x0000xx | xxxxxxx0xxxxxxxxxxxxxxx0xxxxxx
        //    x0000x00xx0x | xxxxxxxxxxxxxxxxx0xxxxxxx0xxxx
        //    ............ | ..............................
        //
        // We denote:
        //
        // A - upper left  block (very sparse, triangular)         -- pivoting rows
        // B - upper right block (partially sparse, rectangular)   -- pivoting rows
        // C -  down left  block (partially  sparse, rectangular)  -- non-pivoting rows
        // D -  down right block (dense, rectangular)              -- non-pivoting rows
        //
        // The algorithm to reduce the matrix is then very simple:
        //
        // 1) row reduce A (B is still partially sparse)
        // 2) annihilate C (D is now almost certainly dense)
        // 3) row echelon & row reduce D
        // 4) row reduce B

        // reverse order for binary searching
        Comparator<DegreeVector> reverseOrder = (a, b) -> factory.ordering.compare(b, a);
        int
                nRows = hPolynomials.size(),
                nColumns = hMonomials.length,
                iRow, iColumn;

        // <- STEP 0: bring matrix to F4-form

        // number of lead-terms in each column (columns with no any lead
        // terms are non-pivoting and can be rearranged)
        int[] columnsLeadTermsFilling = new int[nColumns];
        // detect non-pivoting columns
        int iOldColumnPrev = 0;
        for (HPolynomial<MonomialZp64> hPoly : hPolynomials) {
            iColumn = Arrays.binarySearch(hMonomials, iOldColumnPrev, hMonomials.length, hPoly.hPoly.lt(), reverseOrder);
            iOldColumnPrev = iColumn;
            assert iColumn >= 0;
            ++columnsLeadTermsFilling[iColumn];
        }

        // find non pivoting columns
        TIntArrayList nonPivotColumns = new TIntArrayList();
        for (iColumn = 0; iColumn < nRows + nonPivotColumns.size() && iColumn < nColumns; ++iColumn)
            if (columnsLeadTermsFilling[iColumn] == 0)
                nonPivotColumns.add(iColumn);
        // now we move non-pivoting columns to the right
        // mapping between old and new columns numeration
        int[] nonPivotColumnsArr = nonPivotColumns.toArray();
        int[] columnsRearrangement = ArraysUtil.addAll(
                ArraysUtil.intSetDifference(ArraysUtil.sequence(0, nColumns), nonPivotColumnsArr),
                nonPivotColumnsArr);

        // back mapping between new and old columns numeration
        int[] columnsBackRearrangement = new int[nColumns];
        for (int i = 0; i < nColumns; ++i)
            columnsBackRearrangement[columnsRearrangement[i]] = i;

        // number of non-zero entries in each column
        int[] columnsFilling = new int[nColumns];
        // index of each term in hPolynomials in the hMonomials array
        int[][] mapping = new int[nRows][];
        // estimated row filling of B matrix (number of nonzero elements in each row)
        int[] bRowsFilling = new int[nRows];
        // first iteration: gather info about matrix pattern
        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayBasedPoly<MonomialZp64> hPoly = hPolynomials.get(iRow).hPoly;
            mapping[iRow] = new int[hPoly.size()];
            iOldColumnPrev = 0;
            for (int i = 0; i < hPoly.size(); ++i) {
                MonomialZp64 term = hPoly.get(i);
                // column in old numeration
                int iOldColumn = Arrays.binarySearch(hMonomials, iOldColumnPrev, hMonomials.length, term, reverseOrder);
                iOldColumnPrev = iOldColumn;
                assert iOldColumn >= 0;
                // column in new numeration
                iColumn = columnsBackRearrangement[iOldColumn];
                mapping[iRow][i] = iColumn;

                ++columnsFilling[iColumn];
                if (iColumn >= nRows)
                    ++bRowsFilling[iRow];
            }
        }

        // choose pivoting rows, so that B matrix is maximally sparse (rows with minimal bFillIns)
        TIntArrayList pivots = new TIntArrayList();
        for (iColumn = 0; iColumn < nRows; ++iColumn) {
            int minFillIn = Integer.MAX_VALUE;
            int pivot = -1;
            for (iRow = iColumn; iRow < nRows; ++iRow)
                if (mapping[iRow][0] == iColumn && bRowsFilling[iRow] < minFillIn) {
                    minFillIn = bRowsFilling[iRow];
                    pivot = iRow;
                } else if (pivot != -1 && mapping[iRow][0] != iColumn)
                    break;
            if (pivot == -1)
                break;
            pivots.add(pivot);
        }
        bRowsFilling = null; // prevent further use

        // rearrange rows: move pivots up and non-pivots down
        int nPivotRows = pivots.size();
        for (int i = 0; i < nPivotRows; ++i) {
            int pivot = pivots.get(i);
            Collections.swap(hPolynomials, i, pivot);
            ArraysUtil.swap(mapping, i, pivot);
        }

        for (int i = 0; i < nPivotRows; ++i)
            hPolynomials.get(i).hPoly.monic();
        // the matrix is now is in the desired F4-form

        // <- STEP 1: prepare data structures

        // dense columns in matrices B & D
        int[] bDenseColumns = IntStream.range(nPivotRows, nColumns)
                .filter(i -> 1.0 * columnsFilling[i] / nRows > DENSE_FILLING_THRESHOLD)
                .map(i -> i - nPivotRows)
                .toArray(); // <- it is sorted (for below binary searching)

        // A & C are very sparse
        SparseRowMatrixZp64
                aMatrix = new SparseRowMatrixZp64(ring, nPivotRows, nPivotRows, new int[0]),
                cMatrix = new SparseRowMatrixZp64(ring, nRows - nPivotRows, nPivotRows, new int[0]);

        // sparse matrices B & D
        SparseRowMatrixZp64
                bMatrix = new SparseRowMatrixZp64(ring, nPivotRows, nColumns - nPivotRows, bDenseColumns),
                dMatrix = new SparseRowMatrixZp64(ring, nRows - nPivotRows, nColumns - nPivotRows, bDenseColumns);

        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayBasedPoly<MonomialZp64> hPoly = hPolynomials.get(iRow).hPoly;

            TIntArrayList
                    acSparseCols = new TIntArrayList(),
                    bdSparseCols = new TIntArrayList();
            TLongArrayList
                    acSparseVals = new TLongArrayList(),
                    bdSparseVals = new TLongArrayList();
            long[] bdDenseVals = new long[bDenseColumns.length];
            for (int i = 0; i < hPoly.size(); i++) {
                iColumn = mapping[iRow][i];
                long coefficient = hPoly.get(i).coefficient;
                if (iColumn < nPivotRows) {
                    // element of matrix A or C
                    acSparseCols.add(iColumn);
                    acSparseVals.add(coefficient);
                } else {
                    // element of matrix B or D
                    iColumn -= nPivotRows;
                    int iDense;
                    if ((iDense = Arrays.binarySearch(bDenseColumns, iColumn)) >= 0)
                        // this is dense column (in B or D)
                        bdDenseVals[iDense] = coefficient;
                    else {
                        bdSparseCols.add(iColumn);
                        bdSparseVals.add(coefficient);
                    }
                }
            }

            int[] bdSparseColumns = bdSparseCols.toArray();
            long[] bdSparseValues = bdSparseVals.toArray();
            ArraysUtil.quickSort(bdSparseColumns, bdSparseValues);
            int[] acSparseColumns = acSparseCols.toArray();
            long[] acSparseValues = acSparseVals.toArray();
            ArraysUtil.quickSort(acSparseColumns, acSparseValues);

            if (iRow < nPivotRows) {
                aMatrix.rows[iRow] = new SparseArrayZp64(ring, nPivotRows, new int[0], acSparseColumns, new long[0], acSparseValues);
                bMatrix.rows[iRow] = new SparseArrayZp64(ring, nColumns - nPivotRows, bDenseColumns, bdSparseColumns, bdDenseVals, bdSparseValues);
            } else {
                cMatrix.rows[iRow - nPivotRows] = new SparseArrayZp64(ring, nPivotRows, new int[0], acSparseColumns, new long[0], acSparseValues);
                dMatrix.rows[iRow - nPivotRows] = new SparseArrayZp64(ring, nColumns - nPivotRows, bDenseColumns, bdSparseColumns, bdDenseVals, bdSparseValues);
            }
        }

        // <- STEP 2: row reduce matrix A

        // we start from the last column in matrix A
        for (iRow = nPivotRows - 2; iRow >= 0; --iRow) {
            SparseArrayZp64 aRow = aMatrix.rows[iRow];
            long[] bRow = bMatrix.rows[iRow].toDense();

            for (int i = 0; i < aRow.sparsePositions.length; ++i) {
                iColumn = aRow.sparsePositions[i];
                if (iColumn == iRow) // diagonal
                    continue;
                subtractSparseFromDense(ring, bRow, bMatrix.rows[iColumn], aRow.sparseValues[i]);
            }
            bMatrix.rows[iRow] = new SparseArrayZp64(ring, bMatrix.densePositions, bRow);
        }

        // <-  STEP 3: annihilate matrix C

        for (iRow = 0; iRow < nRows - nPivotRows; ++iRow) {
            SparseArrayZp64 cRow = cMatrix.rows[iRow];
            long[] dRow = dMatrix.rows[iRow].toDense();
            for (int i = 0; i < cRow.sparsePositions.length; ++i) {
                iColumn = cRow.sparsePositions[i];
                subtractSparseFromDense(ring, dRow, bMatrix.rows[iColumn], cRow.sparseValues[i]);
            }
            dMatrix.rows[iRow] = new SparseArrayZp64(ring, dMatrix.densePositions, dRow);
        }

        // <-  STEP 4: compute row reduced echelon form of matrix D

        // this can be optimized (use dense structures, use same structured elimination), but actually
        // it doesn't take too much time

        // make D maximally triangular
        Arrays.sort(dMatrix.rows, Comparator.comparingInt(SparseArrayZp64::firstNonZeroPosition));
        dMatrix.rowReduce();

        // <-  STEP 5: row reduce B

        int dShift = 0;
        for (iRow = 0; iRow < dMatrix.nRows; iRow++) {
            SparseArrayZp64 dRow = dMatrix.rows[iRow];
            iColumn = iRow + dShift;
            if (iColumn >= dMatrix.nColumns)
                break;
            if (dRow.coefficient(iColumn) == 0) {
                --iRow;
                ++dShift;
                continue;
            }
            for (int i = 0; i < bMatrix.nRows; ++i)
                if (bMatrix.rows[i].coefficient(iColumn) != 0)
                    bMatrix.rows[i].subtract(dRow, bMatrix.rows[i].coefficient(iColumn));
        }

        // <- STEP 6: finally form N+ polynomials

        // leading monomials of H-polynomials
        TreeSet<DegreeVector> hLeadMonomials = hPolynomials.stream().map(p -> p.hPoly.lt())
                .collect(Collectors.toCollection(() -> new TreeSet<>(factory.ordering)));

        List<ArrayBasedPoly<MonomialZp64>> nPolynomials = new ArrayList<>();
        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayList<MonomialZp64> candidateList = new ArrayList<>();

            if (iRow < nPivotRows)
                candidateList.add(new MonomialZp64(hMonomials[columnsRearrangement[iRow]], 1L));

            SparseArrayZp64 row = iRow < nPivotRows ? bMatrix.rows[iRow] : dMatrix.rows[iRow - nPivotRows];
            for (int i = 0; i < row.sparsePositions.length; i++) {
                long val = row.sparseValues[i];
                if (val != 0)
                    candidateList.add(new MonomialZp64(hMonomials[columnsRearrangement[nPivotRows + row.sparsePositions[i]]], val));
            }

            for (int i = 0; i < bDenseColumns.length; i++) {
                long val = row.denseValues[i];
                if (val != 0)
                    candidateList.add(new MonomialZp64(hMonomials[columnsRearrangement[nPivotRows + bDenseColumns[i]]], val));
            }

            candidateList.sort(reverseOrder);
            if (!candidateList.isEmpty()) {
                ArrayBasedPoly<MonomialZp64> poly = new ArrayBasedPoly<>(mAlgebra,
                        candidateList.toArray(mAlgebra.createArray(candidateList.size())),
                        factory.nVariables);
                if (poly.lt().coefficient != 1) {
                    long factor = ring.reciprocal(poly.lt().coefficient);
                    for (int i = 0; i < poly.data.length; i++)
                        poly.data[i] = poly.data[i].setCoefficient(ring.multiply(factor, poly.data[i].coefficient));
                }
                assert poly.lt().coefficient == 1;
                nPolynomials.add(poly);
            }
        }
        nPolynomials.sort((a, b) -> reverseOrder.compare(a.lt(), b.lt()));
        // resulting N+ set
        List<ArrayBasedPoly<MonomialZp64>> nPlusPolynomials = new ArrayList<>();
        for (ArrayBasedPoly<MonomialZp64> candidate : nPolynomials) {
            if (!hLeadMonomials.contains(candidate.lt())) {
                // lt is new -> just add
                nPlusPolynomials.add(candidate);
                f4reductions.add(new ArrayList<>(Collections.singletonList(candidate)));
            } else
                // update f4reductions
                for (int iIndex = 0; iIndex < basis.size(); ++iIndex) {
                    ArrayBasedPoly<MonomialZp64> g = basis.get(iIndex);
                    if (g == null)
                        continue;
                    if (candidate.lt().dvDivisibleBy(g.lt())) {
                        List<ArrayBasedPoly<MonomialZp64>> reductions = f4reductions.get(iIndex);
                        boolean reduced = false;
                        for (int i = 0; i < reductions.size(); ++i) {
                            ArrayBasedPoly<MonomialZp64> red = reductions.get(i);
                            if (red.lt().dvEquals(candidate.lt())) {
                                reductions.set(i, candidate);
                                reduced = true;
                                break;
                            }
                        }
                        if (!reduced)
                            reductions.add(candidate);
                    }
                }
        }
        return nPlusPolynomials;
    }

    /** Sparse array implementation */
    static final class SparseArrayZp64 {
        final IntegersZp64 ring;
        final int length;
        final int[] densePositions;
        final long[] denseValues;
        int[] sparsePositions;
        long[] sparseValues;

        SparseArrayZp64(IntegersZp64 ring,
                        int length,
                        int[] densePositions,
                        int[] sparsePositions,
                        long[] denseValues,
                        long[] sparseValues) {
            this.ring = ring;
            this.length = length;
            this.densePositions = densePositions;
            this.sparsePositions = sparsePositions;
            this.denseValues = denseValues;
            this.sparseValues = sparseValues;
            assert isSorted(sparsePositions);
        }

        SparseArrayZp64(IntegersZp64 ring,
                        int[] densePositions,
                        long[] denseArray) {
            this.ring = ring;
            this.densePositions = densePositions;
            this.length = denseArray.length;
            this.denseValues = new long[densePositions.length];
            for (int i = 0; i < densePositions.length; i++)
                denseValues[i] = denseArray[densePositions[i]];

            TIntArrayList sparsePositions = new TIntArrayList();
            TLongArrayList sparseValues = new TLongArrayList();
            for (int i = 0; i < denseArray.length; ++i) {
                if (denseArray[i] == 0)
                    continue;
                if (Arrays.binarySearch(densePositions, i) >= 0)
                    continue;
                sparsePositions.add(i);
                sparseValues.add(denseArray[i]);
            }
            this.sparsePositions = sparsePositions.toArray();
            this.sparseValues = sparseValues.toArray();
        }

        long[] toDense() {
            long[] result = new long[length];
            for (int i = 0; i < densePositions.length; ++i)
                result[densePositions[i]] = denseValues[i];
            for (int i = 0; i < sparsePositions.length; ++i)
                result[sparsePositions[i]] = sparseValues[i];
            return result;
        }

        void subtract(SparseArrayZp64 pivot, long factor, int iColumn, int firstDense) {
            if (factor == 0)
                return;
            assert pivot.densePositions == densePositions;
            long negFactor = ring.negate(factor);

            // adding dense parts
            for (int i = firstDense; i < denseValues.length; i++)
                denseValues[i] = ring.subtract(denseValues[i], ring.multiply(factor, pivot.denseValues[i]));

            // subtracting sparse parts
            int[] pivCols = pivot.sparsePositions;
            long[] pivVals = pivot.sparseValues;

            int firstSparse = ArraysUtil.binarySearch1(sparsePositions, iColumn);

            // resulting non-zero columns
            TIntArrayList resCols = new TIntArrayList(sparsePositions.length + pivCols.length);
            TLongArrayList resVals = new TLongArrayList(sparsePositions.length + pivCols.length);

            resCols.add(sparsePositions, 0, firstSparse);
            resVals.add(sparseValues, 0, firstSparse);

            int iSel = firstSparse, iPiv = 0;
            while (iSel < sparsePositions.length && iPiv < pivCols.length) {
                int
                        selCol = sparsePositions[iSel],
                        othCol = pivCols[iPiv];

                if (selCol == othCol) {
                    long subtract = ring.subtract(sparseValues[iSel], ring.multiply(factor, pivVals[iPiv]));
                    if (subtract != 0) {
                        resCols.add(selCol);
                        resVals.add(subtract);
                    }

                    ++iSel;
                    ++iPiv;
                } else if (selCol < othCol) {
                    resCols.add(selCol);
                    resVals.add(sparseValues[iSel]);

                    ++iSel;
                } else if (selCol > othCol) {
                    resCols.add(othCol);
                    resVals.add(ring.multiply(negFactor, pivVals[iPiv]));

                    ++iPiv;
                }
            }

            if (iSel < sparsePositions.length)
                for (; iSel < sparsePositions.length; ++iSel) {
                    resCols.add(sparsePositions[iSel]);
                    resVals.add(sparseValues[iSel]);
                }

            if (iPiv < pivCols.length)
                for (; iPiv < pivCols.length; ++iPiv) {
                    resCols.add(pivCols[iPiv]);
                    resVals.add(ring.multiply(negFactor, pivVals[iPiv]));
                }

            sparsePositions = resCols.toArray();
            sparseValues = resVals.toArray();
        }

        void subtract(SparseArrayZp64 pivot, long factor) {
            subtract(pivot, factor, 0, 0);
        }

        void multiply(long factor) {
            if (factor == 1)
                return;
            for (int i = 0; i < sparseValues.length; ++i)
                sparseValues[i] = ring.multiply(sparseValues[i], factor);
            for (int i = 0; i < denseValues.length; ++i)
                denseValues[i] = ring.multiply(denseValues[i], factor);
        }

        long coefficient(int iRow) {
            int index = Arrays.binarySearch(sparsePositions, iRow);
            if (index >= 0)
                return sparseValues[index];
            index = Arrays.binarySearch(densePositions, iRow);
            if (index >= 0)
                return denseValues[index];
            return 0;
        }

        void multiply(int iRow, long value) {
            int index = Arrays.binarySearch(sparsePositions, iRow);
            if (index >= 0)
                sparseValues[index] = ring.multiply(sparseValues[index], value);
            else {
                index = Arrays.binarySearch(densePositions, iRow);
                if (index >= 0)
                    denseValues[index] = ring.multiply(denseValues[index], value);
            }
        }

        void subtract(int iRow, long value) {
            if (value == 0)
                return;

            int index = Arrays.binarySearch(densePositions, iRow);
            if (index >= 0)
                denseValues[index] = ring.subtract(denseValues[index], value);
            else {
                index = Arrays.binarySearch(sparsePositions, iRow);
                if (index >= 0) {
                    sparseValues[index] = ring.subtract(sparseValues[index], value);
                    if (sparseValues[index] == 0) {
                        sparsePositions = ArraysUtil.remove(sparsePositions, index);
                        sparseValues = ArraysUtil.remove(sparseValues, index);
                    }
                } else {
                    index = ~index;
                    sparsePositions = ArraysUtil.insert(sparsePositions, index, iRow);
                    sparseValues = ArraysUtil.insert(sparseValues, index, ring.negate(value));
                }
            }
        }

        int firstNonZeroPosition() {
            int firstSparse = sparsePositions.length != 0 ? sparsePositions[0] : Integer.MAX_VALUE;
            for (int i = 0; i < densePositions.length; ++i)
                if (denseValues[i] != 0)
                    return Math.min(densePositions[i], firstSparse);
            return firstSparse;
        }
    }

    // denseArray - factor * sparseArray
    static void subtractSparseFromDense(IntegersZp64 ring, long[] denseArray, SparseArrayZp64 sparseArray, long factor) {
        for (int i = 0; i < sparseArray.densePositions.length; i++)
            denseArray[sparseArray.densePositions[i]] = ring.subtract(denseArray[sparseArray.densePositions[i]], ring.multiply(factor, sparseArray.denseValues[i]));
        for (int i = 0; i < sparseArray.sparsePositions.length; i++)
            denseArray[sparseArray.sparsePositions[i]] = ring.subtract(denseArray[sparseArray.sparsePositions[i]], ring.multiply(factor, sparseArray.sparseValues[i]));
    }

    static final class SparseColumnMatrixZp64 {
        final IntegersZp64 ring;
        final int nRows, nColumns;
        final int[] densePositions;
        final SparseArrayZp64[] columns;

        SparseColumnMatrixZp64(IntegersZp64 ring, int nRows, int nColumns, int[] densePositions) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.columns = new SparseArrayZp64[nColumns];
        }

        void multiplyRow(int iRow, long value) {
            if (value != 1)
                for (int i = 0; i < nColumns; ++i)
                    columns[i].multiply(iRow, value);
        }

        SparseRowMatrixZp64 toRowMatrix(int[] densePositions) {
            SparseRowMatrixZp64 rowMatrix = new SparseRowMatrixZp64(ring, nRows, nColumns, densePositions);
            TIntArrayList[] sparseColumns = new TIntArrayList[nRows];
            TLongArrayList[] sparseValues = new TLongArrayList[nRows];
            long[][] denseValues = new long[nRows][densePositions.length];

            for (int iRow = 0; iRow < nRows; ++iRow) {
                sparseColumns[iRow] = new TIntArrayList();
                sparseValues[iRow] = new TLongArrayList();
            }

            for (int iColumn = 0; iColumn < nColumns; ++iColumn) {
                SparseArrayZp64 column = columns[iColumn];
                int iDenseColumn = Arrays.binarySearch(densePositions, iColumn);
                if (iDenseColumn >= 0) {
                    for (int i = 0; i < column.densePositions.length; i++)
                        denseValues[column.densePositions[i]][iDenseColumn] = column.denseValues[i];
                    for (int i = 0; i < column.sparsePositions.length; ++i)
                        denseValues[column.sparsePositions[i]][iDenseColumn] = column.sparseValues[i];
                } else {
                    for (int i = 0; i < column.densePositions.length; i++) {
                        sparseColumns[column.densePositions[i]].add(iColumn);
                        sparseValues[column.densePositions[i]].add(column.denseValues[i]);
                    } for (int i = 0; i < column.sparsePositions.length; ++i) {
                        sparseColumns[column.sparsePositions[i]].add(iColumn);
                        sparseValues[column.sparsePositions[i]].add(column.sparseValues[i]);
                    }
                }
            }

            for (int iRow = 0; iRow < nRows; ++iRow)
                rowMatrix.rows[iRow] = new SparseArrayZp64(ring, nColumns, densePositions, sparseColumns[iRow].toArray(), denseValues[iRow], sparseValues[iRow].toArray());

            return rowMatrix;
        }
    }

    static final class SparseRowMatrixZp64 {
        final IntegersZp64 ring;
        final int nRows, nColumns;
        final int[] densePositions;
        final SparseArrayZp64[] rows;

        SparseRowMatrixZp64(IntegersZp64 ring, int nRows, int nColumns, int[] densePositions) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.rows = new SparseArrayZp64[nRows];
        }

        SparseRowMatrixZp64(IntegersZp64 ring, int nRows, int nColumns, int[] densePositions, SparseArrayZp64[] rows) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.rows = rows;
        }

        SparseRowMatrixZp64 range(int from, int to) {
            return new SparseRowMatrixZp64(ring, to - from, nColumns, densePositions, Arrays.copyOfRange(rows, from, to));
        }

        long[][] denseMatrix() {
            long[][] result = new long[rows.length][nColumns];
            for (int iRow = 0; iRow < rows.length; ++iRow) {
                SparseArrayZp64 row = rows[iRow];
                for (int i = 0; i < row.sparsePositions.length; i++)
                    result[iRow][row.sparsePositions[i]] = row.sparseValues[i];
                for (int i = 0; i < densePositions.length; i++)
                    result[iRow][densePositions[i]] = row.denseValues[i];
            }
            return result;
        }


        // return rank
        int rowReduce() {
            // Gaussian elimination
            int nZeroRows = 0;
            for (int iCol = 0, to = rows.length; iCol < to; ++iCol) {
                int iRow = iCol - nZeroRows;
                int pivotIndex = -1;

                for (int i = iRow; i < rows.length; ++i) {
                    if (rows[i].coefficient(iCol) == 0)
                        continue;
                    if (pivotIndex == -1) {
                        pivotIndex = i;
                        continue;
                    }
                    if (rows[i].sparsePositions.length < rows[pivotIndex].sparsePositions.length)
                        pivotIndex = i;
                }

                if (pivotIndex == -1) {
                    ++nZeroRows;
                    to = Math.min(nColumns, rows.length + nZeroRows);
                    continue;
                }

                ArraysUtil.swap(rows, pivotIndex, iRow);
                SparseArrayZp64 pivot = rows[iRow];
                long diagonalValue = pivot.coefficient(iCol);

                // row-reduction
                pivot.multiply(ring.reciprocal(diagonalValue));

                int firstDense = ArraysUtil.binarySearch1(densePositions, iCol);
                for (int row = 0; row < rows.length; ++row) {
                    if (row == iRow)
                        continue;

                    long value = rows[row].coefficient(iCol);
                    if (value == 0)
                        continue;

                    rows[row].subtract(pivot, value, iCol, firstDense);
                }
            }
            return Math.min(nRows, nColumns) - nZeroRows;
        }
    }


    /* ******************************************* F4 generic linear algebra ******************************************* */

    @SuppressWarnings("unchecked")
    private static <E> List<ArrayBasedPoly<Monomial<E>>> reduceMatrixE(
            MultivariatePolynomial<E> factory,
            List<ArrayBasedPoly<Monomial<E>>> basis,
            List<HPolynomial<Monomial<E>>> hPolynomials,
            DegreeVector[] hMonomials,
            List<List<ArrayBasedPoly<Monomial<E>>>> f4reductions) {
        Ring<E> ring = factory.ring;
        IMonomialAlgebra<Monomial<E>> mAlgebra = factory.monomialAlgebra;

        // We use the structured Gaussian elimination strategy as described in
        // J.-C. Faugere & S. Lachartre, PASCO'10 https://doi.org/10.1145/1837210.1837225
        // "Parallel Gaussian Elimination for Gröbner bases computations in finite fields"
        //
        // By swapping the rows and non-pivoting columns, each matrix in F4
        // can be rewritten in the following form (F4-form):
        //
        //    \x0x00xx000x | x0x00xx0000x0x0x0xx000xx000xx0
        //    0\x0x0x00xx0 | 0xx0000x0xxx0x00xx0x0000xx0000
        //    00\x00x000x0 | 0x0x0000x0x0xx00xx0x00x0x0xx00
        //    000\xx0x0x00 | xx0xxx00x000x0x0xx00x0x0xx000x
        //    0000\xx0x0x0 | x0000xx0x00x0xxx0xx0000x000xx0
        //    00000\x0000x | 00x0000x0x0x0xx0xx0xx000xx0000
        //    000000\xx00x | 0x0x000x00x0xxx0xx00xxx0x0xx00
        //    0000000\x0x0 | xx00xx00xx00x000xx0xx00x0x000x
        //    ............ | ..............................
        //    -------------+-------------------------------
        //    0xx000x0x0xx | xxxxxx0xxxxxxx0xxxxxxxxxxxxxxx
        //    x0xx000x0x00 | xxxx0xxxxxxxxxxxxxx0xxxxxxxxxx
        //    00x00x0000xx | xxxxxxx0xxxxxxxxxxxxxxx0xxxxxx
        //    x0000x00xx0x | xxxxxxxxxxxxxxxxx0xxxxxxx0xxxx
        //    ............ | ..............................
        //
        // We denote:
        //
        // A - upper left  block (very sparse, triangular)         -- pivoting rows
        // B - upper right block (partially sparse, rectangular)   -- pivoting rows
        // C -  down left  block (partially  sparse, rectangular)  -- non-pivoting rows
        // D -  down right block (dense, rectangular)              -- non-pivoting rows
        //
        // The algorithm to reduce the matrix is then very simple:
        //
        // 1) row reduce A (B is still partially sparse)
        // 2) annihilate C (D is now almost certainly dense)
        // 3) row echelon & row reduce D
        // 4) row reduce B

        // reverse order for binary searching
        Comparator<DegreeVector> reverseOrder = (a, b) -> factory.ordering.compare(b, a);
        int
                nRows = hPolynomials.size(),
                nColumns = hMonomials.length,
                iRow, iColumn;

        // <- STEP 0: bring matrix to F4-form

        // bring each poly to canonical form (either monic or primitive)
        hPolynomials.forEach(h -> h.hPoly.canonical());

        // number of lead-terms in each column (columns with no any lead
        // terms are non-pivoting and can be rearranged)
        int[] columnsLeadTermsFilling = new int[nColumns];
        // detect non-pivoting columns
        int iOldColumnPrev = 0;
        for (HPolynomial<Monomial<E>> hPoly : hPolynomials) {
            iColumn = Arrays.binarySearch(hMonomials, iOldColumnPrev, hMonomials.length, hPoly.hPoly.lt(), reverseOrder);
            iOldColumnPrev = iColumn;
            assert iColumn >= 0;
            ++columnsLeadTermsFilling[iColumn];
        }

        // find non pivoting columns
        TIntArrayList nonPivotColumns = new TIntArrayList();
        for (iColumn = 0; iColumn < nRows + nonPivotColumns.size() && iColumn < nColumns; ++iColumn)
            if (columnsLeadTermsFilling[iColumn] == 0)
                nonPivotColumns.add(iColumn);
        // now we move non-pivoting columns to the right
        // mapping between old and new columns numeration
        int[] nonPivotColumnsArr = nonPivotColumns.toArray();
        int[] columnsRearrangement = ArraysUtil.addAll(
                ArraysUtil.intSetDifference(ArraysUtil.sequence(0, nColumns), nonPivotColumnsArr),
                nonPivotColumnsArr);

        // back mapping between new and old columns numeration
        int[] columnsBackRearrangement = new int[nColumns];
        for (int i = 0; i < nColumns; ++i)
            columnsBackRearrangement[columnsRearrangement[i]] = i;

        // number of non-zero entries in each column
        int[] columnsFilling = new int[nColumns];
        // index of each term in hPolynomials in the hMonomials array
        int[][] mapping = new int[nRows][];
        // estimated row filling of B matrix (number of nonzero elements in each row)
        int[] bRowsFilling = new int[nRows];
        // first iteration: gather info about matrix pattern
        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayBasedPoly<Monomial<E>> hPoly = hPolynomials.get(iRow).hPoly;
            mapping[iRow] = new int[hPoly.size()];
            iOldColumnPrev = 0;
            for (int i = 0; i < hPoly.size(); ++i) {
                Monomial<E> term = hPoly.get(i);
                // column in old numeration
                int iOldColumn = Arrays.binarySearch(hMonomials, iOldColumnPrev, hMonomials.length, term, reverseOrder);
                iOldColumnPrev = iOldColumn;
                assert iOldColumn >= 0;
                // column in new numeration
                iColumn = columnsBackRearrangement[iOldColumn];
                mapping[iRow][i] = iColumn;

                ++columnsFilling[iColumn];
                if (iColumn >= nRows)
                    ++bRowsFilling[iRow];
            }
        }

        // choose pivoting rows, so that B matrix is maximally sparse (rows with minimal bFillIns)
        // and lead terms of pivoting polys are units (if possible)
        TIntArrayList pivots = new TIntArrayList();
        for (iColumn = 0; iColumn < nRows; ++iColumn) {
            int minFillIn = Integer.MAX_VALUE;
            int pivot = -1;
            boolean unitLeadTerm = false;
            for (iRow = iColumn; iRow < nRows; ++iRow)
                if (mapping[iRow][0] == iColumn) {
                    // try to find pivot with unit lead term
                    boolean ult = ring.isUnit(hPolynomials.get(iRow).hPoly.lt().coefficient);
                    if (!unitLeadTerm && ult) {
                        minFillIn = bRowsFilling[iRow];
                        pivot = iRow;
                        unitLeadTerm = true;
                    } else if ((unitLeadTerm == ult) && bRowsFilling[iRow] < minFillIn) {
                        minFillIn = bRowsFilling[iRow];
                        pivot = iRow;
                    }
                    assert pivot != -1;
                } else if (pivot != -1 && mapping[iRow][0] != iColumn)
                    break;
            if (pivot == -1)
                break;
            pivots.add(pivot);
        }
        bRowsFilling = null; // prevent further use

        // rearrange rows: move pivots up and non-pivots down
        int nPivotRows = pivots.size();
        for (int i = 0; i < nPivotRows; ++i) {
            int pivot = pivots.get(i);
            Collections.swap(hPolynomials, i, pivot);
            ArraysUtil.swap(mapping, i, pivot);
        }

        // the matrix is in the desired F4-form

        // <- STEP 1: prepare data structures

        // dense columns in matrices B & D
        int[] bDenseColumns = IntStream.range(nPivotRows, nColumns)
                .filter(i -> 1.0 * columnsFilling[i] / nRows > DENSE_FILLING_THRESHOLD)
                .map(i -> i - nPivotRows)
                .toArray(); // <- it is sorted (for below binary searching)

        // A & C are very sparse
        SparseRowMatrix<E>
                aMatrix = new SparseRowMatrix<>(ring, nPivotRows, nPivotRows, new int[0]),
                cMatrix = new SparseRowMatrix<>(ring, nRows - nPivotRows, nPivotRows, aMatrix.densePositions);

        // sparse matrices B & D
        SparseRowMatrix<E>
                bMatrix = new SparseRowMatrix<>(ring, nPivotRows, nColumns - nPivotRows, bDenseColumns),
                dMatrix = new SparseRowMatrix<>(ring, nRows - nPivotRows, nColumns - nPivotRows, bDenseColumns);

        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayBasedPoly<Monomial<E>> hPoly = hPolynomials.get(iRow).hPoly;

            TIntArrayList
                    acSparseCols = new TIntArrayList(),
                    bdSparseCols = new TIntArrayList();
            ArrayList<E>
                    acSparseVals = new ArrayList<>(),
                    bdSparseVals = new ArrayList<>();
            E[] bdDenseVals = ring.createZeroesArray(bDenseColumns.length);
            for (int i = 0; i < hPoly.size(); i++) {
                iColumn = mapping[iRow][i];
                E coefficient = hPoly.get(i).coefficient;
                if (iColumn < nPivotRows) {
                    // element of matrix A or C
                    acSparseCols.add(iColumn);
                    acSparseVals.add(coefficient);
                } else {
                    // element of matrix B or D
                    iColumn -= nPivotRows;
                    int iDense;
                    if ((iDense = Arrays.binarySearch(bDenseColumns, iColumn)) >= 0)
                        // this is dense column (in B or D)
                        bdDenseVals[iDense] = coefficient;
                    else {
                        bdSparseCols.add(iColumn);
                        bdSparseVals.add(coefficient);
                    }
                }
            }

            int[] bdSparseColumns = bdSparseCols.toArray();
            E[] bdSparseValues = bdSparseVals.toArray(ring.createArray(bdSparseVals.size()));
            ArraysUtil.quickSort(bdSparseColumns, bdSparseValues);
            int[] acSparseColumns = acSparseCols.toArray();
            E[] acSparseValues = acSparseVals.toArray(ring.createArray(acSparseVals.size()));
            ArraysUtil.quickSort(acSparseColumns, acSparseValues);

            if (iRow < nPivotRows) {
                aMatrix.rows[iRow] = new SparseArray<>(ring, nPivotRows, aMatrix.densePositions, acSparseColumns, ring.createArray(0), acSparseValues);
                bMatrix.rows[iRow] = new SparseArray<>(ring, nColumns - nPivotRows, bDenseColumns, bdSparseColumns, bdDenseVals, bdSparseValues);
            } else {
                cMatrix.rows[iRow - nPivotRows] = new SparseArray<>(ring, nPivotRows, cMatrix.densePositions, acSparseColumns, ring.createArray(0), acSparseValues);
                dMatrix.rows[iRow - nPivotRows] = new SparseArray<>(ring, nColumns - nPivotRows, bDenseColumns, bdSparseColumns, bdDenseVals, bdSparseValues);
            }
        }

        // <- STEP 2: row reduce matrix A

        // we start from the last column in matrix A
        for (iRow = nPivotRows - 2; iRow >= 0; --iRow) {
            SparseArray<E> aRow = aMatrix.rows[iRow];
            E[] bRow = bMatrix.rows[iRow].toDense();

            for (int i = aRow.sparsePositions.length - 1; i >= 0; --i) {
                iColumn = aRow.sparsePositions[i];
                if (iColumn == iRow)
                    continue; // diagonal
                assert iColumn > iRow;
                SparseArray<E>
                        // pivot row in A
                        aPivotRow = aMatrix.rows[iColumn],
                        // corresponding pivot row in B
                        bPivotRow = bMatrix.rows[iColumn];

                // non-diagonal value in A (iRow, iColumn)
                E aNonDiagonal = aRow.sparseValues[i];
                // corresponding pivoting value (iColumn, iColumn) in A
                E aPivot = aPivotRow.coefficient(iColumn);
                assert !ring.isZero(aPivot);

                E // compute LCM and correction factors
                        lcm = ring.lcm(aNonDiagonal, aPivot),
                        // correction factor for currently reducing row
                        rowFactor = ring.divideExact(lcm, aNonDiagonal),
                        // correction factor for pivoting row
                        pivotFactor = ring.divideExact(lcm, aPivot);

                // bRow = rowFactor * bRow -  pivotFactor * bPivotRow
                subtractSparseFromDense(ring, bRow, rowFactor, bPivotRow, pivotFactor);
                // correct aRow
                aRow.multiply(rowFactor);
            }
            // set row in B
            bMatrix.rows[iRow] = new SparseArray(ring, bMatrix.densePositions, bRow);
            // diagonal value in A row
            E aRowDiagonalValue = aRow.coefficient(iRow);
            assert !ring.isZero(aRowDiagonalValue);
            // common content in the AB row
            E abRowContent = bMatrix.rows[iRow].content(aRowDiagonalValue);
            bMatrix.rows[iRow].divideExact(abRowContent);
            // recreate row of A (with single diagonal element)
            aRow.sparsePositions = new int[]{iRow};
            aRow.sparseValues = ring.createArray(ring.divideExact(aRowDiagonalValue, abRowContent));
        }

        // <-  STEP 3: annihilate matrix C

        for (iRow = 0; iRow < nRows - nPivotRows; ++iRow) {
            SparseArray<E> cRow = cMatrix.rows[iRow];
            E[] dRow = dMatrix.rows[iRow].toDense();
            for (int i = cRow.sparsePositions.length - 1; i >= 0; --i) {
                iColumn = cRow.sparsePositions[i];

                SparseArray<E>
                        // pivot row in A
                        aPivotRow = aMatrix.rows[iColumn],
                        // corresponding pivot row in B
                        bPivotRow = bMatrix.rows[iColumn];

                // value in C (iRow, iColumn)
                E cElement = cRow.sparseValues[i];
                // corresponding pivoting value (iColumn, iColumn)
                E aPivot = aPivotRow.coefficient(iColumn);
                assert !ring.isZero(aPivot);

                E // compute LCM and correction factors
                        lcm = ring.lcm(cElement, aPivot),
                        // correction factor for currently reducing row
                        dFactor = ring.divideExact(lcm, cElement),
                        // correction factor for pivoting row
                        bFactor = ring.divideExact(lcm, aPivot);

                // bRow = rowFactor * bRow -  pivotFactor * bPivotRow
                subtractSparseFromDense(ring, dRow, dFactor, bPivotRow, bFactor);
                // correct cRow
                cRow.multiply(dFactor);
            }
            dMatrix.rows[iRow] = new SparseArray(ring, dMatrix.densePositions, dRow);
            dMatrix.rows[iRow].primitivePart();
        }

        // <-  STEP 4: compute row reduced echelon form of matrix D

        // this can be optimized (use dense structures, use same structured elimination), but actually
        // it doesn't take too much time

        // make D maximally triangular
        Arrays.sort(dMatrix.rows, Comparator.comparingInt(SparseArray::firstNonZeroPosition));
        dMatrix.rowReduce();

        // <-  STEP 5: row reduce B

        int dShift = 0;
        for (iRow = 0; iRow < dMatrix.nRows; iRow++) {
            SparseArray<E> dPivotRow = dMatrix.rows[iRow];
            iColumn = iRow + dShift;
            if (iColumn >= dMatrix.nColumns)
                break;
            if (ring.isZero(dPivotRow.coefficient(iColumn))) {
                --iRow;
                ++dShift;
                continue;
            }
            for (int i = 0; i < bMatrix.nRows; ++i)
                if (!ring.isZero(bMatrix.rows[i].coefficient(iColumn))) {
                    SparseArray<E>
                            bRow = bMatrix.rows[i],
                            aRow = aMatrix.rows[i];

                    E       // pivot value (D matrix)
                            dPivot = dPivotRow.coefficient(iColumn),
                            // element to annihilate (in B matrix)
                            bElement = bRow.coefficient(iColumn),
                            // compute LCM and correction factors,
                            lcm = ring.lcm(bElement, dPivot),
                            // correction factor for currently reducing row
                            bFactor = ring.divideExact(lcm, bElement),
                            // correction factor for pivoting row
                            dFactor = ring.divideExact(lcm, dPivot);

                    // reduce B row
                    bRow.multiply(bFactor);
                    bRow.subtract(dPivotRow, dFactor);
                    // correct corresponding A row
                    aRow.multiply(bFactor);

                    // make that AB row primitive (remove common content)
                    E abContent = bRow.content(aMatrix.rows[i].coefficient(i));
                    bRow.divideExact(abContent);
                    aRow.divideExact(abContent);

                    assert ring.isZero(bRow.coefficient(iColumn));
                }
        }

        // <- STEP 6: finally form N+ polynomials

        // leading monomials of H-polynomials
        TreeSet<DegreeVector> hLeadMonomials = hPolynomials.stream().map(p -> p.hPoly.lt())
                .collect(Collectors.toCollection(() -> new TreeSet<>(factory.ordering)));

        List<ArrayBasedPoly<Monomial<E>>> nPolynomials = new ArrayList<>();
        for (iRow = 0; iRow < nRows; ++iRow) {
            ArrayList<Monomial<E>> candidateList = new ArrayList<>();

            if (iRow < nPivotRows) {
                E cf = aMatrix.rows[iRow].coefficient(iRow);
                assert !ring.isZero(cf);
                candidateList.add(new Monomial<>(hMonomials[columnsRearrangement[iRow]], cf));
            }

            SparseArray<E> row = iRow < nPivotRows ? bMatrix.rows[iRow] : dMatrix.rows[iRow - nPivotRows];
            for (int i = 0; i < row.sparsePositions.length; i++) {
                E val = row.sparseValues[i];
                if (!ring.isZero(val))
                    candidateList.add(new Monomial<>(hMonomials[columnsRearrangement[nPivotRows + row.sparsePositions[i]]], val));
            }

            for (int i = 0; i < bDenseColumns.length; i++) {
                E val = row.denseValues[i];
                if (!ring.isZero(val))
                    candidateList.add(new Monomial<>(hMonomials[columnsRearrangement[nPivotRows + bDenseColumns[i]]], val));
            }

            candidateList.sort(reverseOrder);
            if (!candidateList.isEmpty()) {
                ArrayBasedPoly<Monomial<E>> poly = new ArrayBasedPoly<>(mAlgebra,
                        candidateList.toArray(mAlgebra.createArray(candidateList.size())),
                        factory.nVariables);
                poly.canonical();
                nPolynomials.add(poly);
            }
        }
        nPolynomials.sort((a, b) -> reverseOrder.compare(a.lt(), b.lt()));
        // resulting N+ set
        List<ArrayBasedPoly<Monomial<E>>> nPlusPolynomials = new ArrayList<>();
        for (ArrayBasedPoly<Monomial<E>> candidate : nPolynomials) {
            if (!hLeadMonomials.contains(candidate.lt())) {
                // lt is new -> just add
                nPlusPolynomials.add(candidate);
                f4reductions.add(new ArrayList<>(Collections.singletonList(candidate)));
            } else
                // update f4reductions
                for (int iIndex = 0; iIndex < basis.size(); ++iIndex) {
                    ArrayBasedPoly<Monomial<E>> g = basis.get(iIndex);
                    if (g == null)
                        continue;
                    if (candidate.lt().dvDivisibleBy(g.lt())) {
                        List<ArrayBasedPoly<Monomial<E>>> reductions = f4reductions.get(iIndex);
                        boolean reduced = false;
                        for (int i = 0; i < reductions.size(); ++i) {
                            ArrayBasedPoly<Monomial<E>> red = reductions.get(i);
                            if (red.lt().dvEquals(candidate.lt())) {
                                reductions.set(i, candidate);
                                reduced = true;
                                break;
                            }
                        }
                        if (!reduced)
                            reductions.add(candidate);
                    }
                }
        }
        return nPlusPolynomials;
    }

    /** Sparse array implementation */
    static final class SparseArray<E> {
        final Ring<E> ring;
        final int length;
        final int[] densePositions;
        final E[] denseValues;
        int[] sparsePositions;
        E[] sparseValues;

        SparseArray(Ring<E> ring,
                    int length,
                    int[] densePositions,
                    int[] sparsePositions,
                    E[] denseValues,
                    E[] sparseValues) {
            this.ring = ring;
            this.length = length;
            this.densePositions = densePositions;
            this.sparsePositions = sparsePositions;
            this.denseValues = denseValues;
            this.sparseValues = sparseValues;
            assert isSorted(sparsePositions) : Arrays.toString(sparsePositions);
        }

        SparseArray(Ring<E> ring,
                    int[] densePositions,
                    E[] denseArray) {
            this.ring = ring;
            this.densePositions = densePositions;
            this.length = denseArray.length;
            this.denseValues = ring.createArray(densePositions.length);
            for (int i = 0; i < densePositions.length; i++)
                denseValues[i] = denseArray[densePositions[i]];

            TIntArrayList sparsePositions = new TIntArrayList();
            ArrayList<E> sparseValues = new ArrayList<>();
            for (int i = 0; i < denseArray.length; ++i) {
                if (ring.isZero(denseArray[i]))
                    continue;
                if (Arrays.binarySearch(densePositions, i) >= 0)
                    continue;
                sparsePositions.add(i);
                sparseValues.add(denseArray[i]);
            }
            this.sparsePositions = sparsePositions.toArray();
            this.sparseValues = sparseValues.toArray(ring.createArray(sparseValues.size()));
            assert isSorted(this.sparsePositions) : Arrays.toString(this.sparsePositions);
        }

        E[] toDense() {
            E[] result = ring.createZeroesArray(length);
            for (int i = 0; i < densePositions.length; ++i)
                result[densePositions[i]] = denseValues[i];
            for (int i = 0; i < sparsePositions.length; ++i)
                result[sparsePositions[i]] = sparseValues[i];
            return result;
        }

        void subtract(SparseArray<E> pivot, E factor, int iColumn, int firstDense) {
            if (ring.isZero(factor))
                return;
            assert pivot.densePositions == densePositions;
            E negFactor = ring.negate(factor);

            // adding dense parts
            for (int i = firstDense; i < denseValues.length; i++)
                denseValues[i] = ring.subtract(denseValues[i], ring.multiply(factor, pivot.denseValues[i]));

            // subtracting sparse parts
            int[] pivCols = pivot.sparsePositions;
            E[] pivVals = pivot.sparseValues;

            int firstSparse = ArraysUtil.binarySearch1(sparsePositions, iColumn);

            // resulting non-zero columns
            TIntArrayList resCols = new TIntArrayList(sparsePositions.length + pivCols.length);
            ArrayList<E> resVals = new ArrayList<>(sparsePositions.length + pivCols.length);

            resCols.add(sparsePositions, 0, firstSparse);
            resVals.addAll(Arrays.asList(sparseValues).subList(0, firstSparse));

            int iSel = firstSparse, iPiv = 0;
            while (iSel < sparsePositions.length && iPiv < pivCols.length) {
                int
                        selCol = sparsePositions[iSel],
                        othCol = pivCols[iPiv];

                if (selCol == othCol) {
                    E subtract = ring.subtract(sparseValues[iSel], ring.multiply(factor, pivVals[iPiv]));
                    if (!ring.isZero(subtract)) {
                        resCols.add(selCol);
                        resVals.add(subtract);
                    }

                    ++iSel;
                    ++iPiv;
                } else if (selCol < othCol) {
                    resCols.add(selCol);
                    resVals.add(sparseValues[iSel]);

                    ++iSel;
                } else if (selCol > othCol) {
                    resCols.add(othCol);
                    resVals.add(ring.multiply(negFactor, pivVals[iPiv]));

                    ++iPiv;
                }
            }

            if (iSel < sparsePositions.length)
                for (; iSel < sparsePositions.length; ++iSel) {
                    resCols.add(sparsePositions[iSel]);
                    resVals.add(sparseValues[iSel]);
                }

            if (iPiv < pivCols.length)
                for (; iPiv < pivCols.length; ++iPiv) {
                    resCols.add(pivCols[iPiv]);
                    resVals.add(ring.multiply(negFactor, pivVals[iPiv]));
                }

            sparsePositions = resCols.toArray();
            assert resCols.size() == new TIntArrayList(resCols).size();
            sparseValues = resVals.toArray(ring.createArray(resVals.size()));
            assert isSorted(sparsePositions) : Arrays.toString(sparsePositions);
        }

        void subtract(SparseArray<E> pivot, E factor) {
            subtract(pivot, factor, 0, 0);
        }

        void multiply(E factor) {
            if (ring.isOne(factor))
                return;
            for (int i = 0; i < sparseValues.length; ++i)
                sparseValues[i] = ring.multiply(sparseValues[i], factor);
            for (int i = 0; i < denseValues.length; ++i)
                denseValues[i] = ring.multiply(denseValues[i], factor);
            assert isSorted(sparsePositions) : Arrays.toString(sparsePositions);
        }

        void divideExact(E factor) {
            if (ring.isOne(factor))
                return;
            for (int i = 0; i < sparseValues.length; ++i)
                sparseValues[i] = ring.divideExact(sparseValues[i], factor);
            for (int i = 0; i < denseValues.length; ++i)
                denseValues[i] = ring.divideExact(denseValues[i], factor);
        }

        E content(E el) {
            if (ring.isField())
                return ring.getOne();
            ArrayList<E> els = new ArrayList<>();
            els.add(el);
            els.addAll(Arrays.asList(sparseValues));
            els.addAll(Arrays.asList(denseValues));
            E gcd = ring.gcd(els);
            if (ring.isZero(gcd))
                return ring.getOne();
            return gcd;
        }

        E content() {
            return content(ring.getZero());
        }

        void primitivePart() {
            divideExact(content());
        }

        E coefficient(int iRow) {
            int index = Arrays.binarySearch(sparsePositions, iRow);
            if (index >= 0)
                return sparseValues[index];
            index = Arrays.binarySearch(densePositions, iRow);
            if (index >= 0)
                return denseValues[index];
            return ring.getZero();
        }

        void multiply(int iRow, E value) {
            int index = Arrays.binarySearch(sparsePositions, iRow);
            if (index >= 0)
                sparseValues[index] = ring.multiply(sparseValues[index], value);
            else {
                index = Arrays.binarySearch(densePositions, iRow);
                if (index >= 0)
                    denseValues[index] = ring.multiply(denseValues[index], value);
            }
        }

        void subtract(int iRow, E value) {
            if (ring.isZero(value))
                return;

            int index = Arrays.binarySearch(densePositions, iRow);
            if (index >= 0)
                denseValues[index] = ring.subtract(denseValues[index], value);
            else {
                index = Arrays.binarySearch(sparsePositions, iRow);
                if (index >= 0) {
                    sparseValues[index] = ring.subtract(sparseValues[index], value);
                    if (ring.isZero(sparseValues[index])) {
                        sparsePositions = ArraysUtil.remove(sparsePositions, index);
                        sparseValues = ArraysUtil.remove(sparseValues, index);
                    }
                } else {
                    index = ~index;
                    sparsePositions = ArraysUtil.insert(sparsePositions, index, iRow);
                    sparseValues = ArraysUtil.insert(sparseValues, index, ring.negate(value));
                }
            }
            assert isSorted(sparsePositions) : Arrays.toString(sparsePositions);
        }

        int firstNonZeroPosition() {
            int firstSparse = sparsePositions.length != 0 ? sparsePositions[0] : Integer.MAX_VALUE;
            for (int i = 0; i < densePositions.length; ++i)
                if (!ring.isZero(denseValues[i]))
                    return Math.min(densePositions[i], firstSparse);
            return firstSparse;
        }
    }

    // denseArray - factor * sparseArray
    static <E> void subtractSparseFromDense(Ring<E> ring, E[] denseArray, SparseArray<E> sparseArray, E factor) {
        for (int i = 0; i < sparseArray.densePositions.length; i++)
            denseArray[sparseArray.densePositions[i]] = ring.subtract(denseArray[sparseArray.densePositions[i]], ring.multiply(factor, sparseArray.denseValues[i]));
        for (int i = 0; i < sparseArray.sparsePositions.length; i++)
            denseArray[sparseArray.sparsePositions[i]] = ring.subtract(denseArray[sparseArray.sparsePositions[i]], ring.multiply(factor, sparseArray.sparseValues[i]));
    }

    // denseFactor * denseArray - sparseFactor * sparseArray
    static <E> void subtractSparseFromDense(Ring<E> ring, E[] denseArray, E denseFactor, SparseArray<E> sparseArray, E sparseFactor) {
        if (!ring.isOne(denseFactor))
            for (int i = 0; i < denseArray.length; i++)
                denseArray[i] = ring.multiply(denseArray[i], denseFactor);

        for (int i = 0; i < sparseArray.densePositions.length; i++) {
            int dPosition = sparseArray.densePositions[i];
            denseArray[dPosition] = ring.subtract(denseArray[dPosition], ring.multiply(sparseFactor, sparseArray.denseValues[i]));
        }
        for (int i = 0; i < sparseArray.sparsePositions.length; i++) {
            int sPosition = sparseArray.sparsePositions[i];
            denseArray[sPosition] = ring.subtract(denseArray[sPosition], ring.multiply(sparseFactor, sparseArray.sparseValues[i]));
        }
    }

    static final class SparseColumnMatrix<E> {
        final Ring<E> ring;
        final int nRows, nColumns;
        final int[] densePositions;
        final SparseArray<E>[] columns;

        SparseColumnMatrix(Ring<E> ring, int nRows, int nColumns, int[] densePositions) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.columns = new SparseArray[nColumns];
        }

        void multiplyRow(int iRow, E value) {
            if (!ring.isOne(value))
                for (int i = 0; i < nColumns; ++i)
                    columns[i].multiply(iRow, value);
        }

        SparseRowMatrix<E> toRowMatrix(int[] densePositions) {
            SparseRowMatrix<E> rowMatrix = new SparseRowMatrix<>(ring, nRows, nColumns, densePositions);
            TIntArrayList[] sparseColumns = new TIntArrayList[nRows];
            ArrayList<E>[] sparseValues = new ArrayList[nRows];
            E[][] denseValues = ring.createArray2d(nRows, densePositions.length);

            for (int iRow = 0; iRow < nRows; ++iRow) {
                sparseColumns[iRow] = new TIntArrayList();
                sparseValues[iRow] = new ArrayList<>();
            }

            for (int iColumn = 0; iColumn < nColumns; ++iColumn) {
                SparseArray<E> column = columns[iColumn];
                int iDenseColumn = Arrays.binarySearch(densePositions, iColumn);
                if (iDenseColumn >= 0) {
                    for (int i = 0; i < column.densePositions.length; i++)
                        denseValues[column.densePositions[i]][iDenseColumn] = column.denseValues[i];
                    for (int i = 0; i < column.sparsePositions.length; ++i)
                        denseValues[column.sparsePositions[i]][iDenseColumn] = column.sparseValues[i];
                } else {
                    for (int i = 0; i < column.densePositions.length; i++) {
                        sparseColumns[column.densePositions[i]].add(iColumn);
                        sparseValues[column.densePositions[i]].add(column.denseValues[i]);
                    } for (int i = 0; i < column.sparsePositions.length; ++i) {
                        sparseColumns[column.sparsePositions[i]].add(iColumn);
                        sparseValues[column.sparsePositions[i]].add(column.sparseValues[i]);
                    }
                }
            }

            for (int iRow = 0; iRow < nRows; ++iRow)
                rowMatrix.rows[iRow] = new SparseArray<>(ring, nColumns, densePositions, sparseColumns[iRow].toArray(),
                        denseValues[iRow], sparseValues[iRow].toArray(ring.createArray(sparseValues[iRow].size())));

            return rowMatrix;
        }
    }

    static final class SparseRowMatrix<E> {
        final Ring<E> ring;
        final int nRows, nColumns;
        final int[] densePositions;
        final SparseArray<E>[] rows;

        SparseRowMatrix(Ring<E> ring, int nRows, int nColumns, int[] densePositions) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.rows = new SparseArray[nRows];
        }

        SparseRowMatrix(Ring<E> ring, int nRows, int nColumns, int[] densePositions, SparseArray<E>[] rows) {
            this.ring = ring;
            this.nRows = nRows;
            this.nColumns = nColumns;
            this.densePositions = densePositions;
            this.rows = rows;
        }

        SparseRowMatrix<E> range(int from, int to) {
            return new SparseRowMatrix<>(ring, to - from, nColumns, densePositions, Arrays.copyOfRange(rows, from, to));
        }

        E[][] denseMatrix() {
            E[][] result = ring.createZeroesArray2d(rows.length, nColumns);
            for (int iRow = 0; iRow < rows.length; ++iRow) {
                SparseArray<E> row = rows[iRow];
                for (int i = 0; i < row.sparsePositions.length; i++)
                    result[iRow][row.sparsePositions[i]] = row.sparseValues[i];
                for (int i = 0; i < densePositions.length; i++)
                    result[iRow][densePositions[i]] = row.denseValues[i];
            }
            return result;
        }


        // return rank
        int rowReduce() {
            // Gaussian elimination
            int nZeroRows = 0;
            for (int iCol = 0, to = rows.length; iCol < to; ++iCol) {
                int iRow = iCol - nZeroRows;
                int pivotIndex = -1;
                boolean isUnit = false;
                for (int i = iRow; i < rows.length; ++i) {
                    if (ring.isZero(rows[i].coefficient(iCol)))
                        continue;
                    boolean iu = ring.isUnit(rows[i].coefficient(iRow));
                    if (pivotIndex == -1) {
                        pivotIndex = i;
                        continue;
                    }
                    if (!isUnit && iu) {
                        pivotIndex = i;
                        isUnit = true;
                    } else if ((isUnit == iu) && rows[i].sparsePositions.length < rows[pivotIndex].sparsePositions.length)
                        pivotIndex = i;
                }

                if (pivotIndex == -1) {
                    ++nZeroRows;
                    to = Math.min(nColumns, rows.length + nZeroRows);
                    continue;
                }

                ArraysUtil.swap(rows, pivotIndex, iRow);
                SparseArray<E> pivot = rows[iRow];
                E diagonalValue = pivot.coefficient(iCol);

                // row-reduction
                if (ring.isField())
                    pivot.multiply(ring.reciprocal(diagonalValue));
                else
                    pivot.primitivePart();

                int firstDense = ArraysUtil.binarySearch1(densePositions, iCol);
                for (int row = 0; row < rows.length; ++row) {
                    if (row == iRow)
                        continue;

                    E value = rows[row].coefficient(iCol);
                    if (ring.isZero(value))
                        continue;

                    if (ring.isField())
                        rows[row].subtract(pivot, value, iCol, firstDense);
                    else {
                        E lcm = ring.lcm(diagonalValue, value);
                        rows[row].multiply(ring.divideExact(lcm, value));
                        rows[row].subtract(pivot, ring.divideExact(lcm, diagonalValue), iCol, firstDense);
                        rows[row].primitivePart();
                    }
                    assert ring.isZero(rows[row].coefficient(iCol));
                }
            }
            return Math.min(nRows, nColumns) - nZeroRows;
        }
    }

    private static boolean isSorted(int[] arr) {
        for (int i = 1; i < arr.length; ++i)
            if (arr[i - 1] >= arr[i])
                return false;
        return true;
    }

    /* ************************************** Hilbert-Poincare series ********************************************** */

    /** Check whether all specified generators are monomials */
    public static boolean isMonomialIdeal(List<? extends AMultivariatePolynomial> ideal) {
        return ideal.stream().allMatch(AMultivariatePolynomial::isMonomial);
    }

    /** Check whether ideal is homogeneous */
    public static boolean isHomogeneousIdeal(List<? extends AMultivariatePolynomial> ideal) {
        return ideal.stream().allMatch(AMultivariatePolynomial::isHomogeneous);
    }

    /** List of lead terms of generators */
    public static List<DegreeVector> leadTermsIdeal(List<? extends AMultivariatePolynomial> ideal) {
        return ideal.stream().map(AMultivariatePolynomial::lt).collect(Collectors.toList());
    }

    /**
     * Computes Hilbert-Poincare series of specified homogeneous ideal
     */
    public static HilbertSeries HilbertSeriesOfHomogeneousIdeal(List<? extends AMultivariatePolynomial> ideal) {
        if (!isHomogeneousIdeal(ideal))
            throw new IllegalArgumentException("Not a monomial or homogeneous ideal");
        return HilbertSeries(leadTermsIdeal(ideal));
    }

    /** Minimizes Groebner basis of monomial ideal. The input should be a Groebner basis */
    static void reduceMonomialIdeal(List<DegreeVector> basis) {
        outer:
        for (int i = basis.size() - 1; i >= 1; --i) {
            for (int j = i - 1; j >= 0; --j) {
                DegreeVector pi = basis.get(i), pj = basis.get(j);
                if (pi.dvDivisibleBy(pj)) {
                    basis.remove(i);
                    continue outer;
                }
                if (pj.dvDivisibleBy(pi)) {
                    basis.remove(j);
                    --i;
                    continue;
                }
            }
        }
    }

    /** Computes Hilbert-Poincare series of monomial ideal */
    public static HilbertSeries HilbertSeries(List<DegreeVector> ideal) {
        ideal = new ArrayList<>(ideal);
        reduceMonomialIdeal(ideal);
        UnivariatePolynomial<Rational<BigInteger>> initialNumerator = HilbertSeriesNumerator(ideal).mapCoefficients(Q, c -> new Rational<>(Z, c));
        return new HilbertSeries(initialNumerator, ideal.get(0).nVariables());
    }

    /** initial numerator of Hilbert series */
    private static UnivariatePolynomial<BigInteger> HilbertSeriesNumerator(List<DegreeVector> ideal) {
        UnivariateRing<UnivariatePolynomial<BigInteger>> uniRing = Rings.UnivariateRing(Z);
        if (ideal.isEmpty())
            // zero ideal
            return uniRing.getOne();
        if (ideal.size() == 1 && ideal.get(0).isZeroVector())
            // ideal = ring
            return uniRing.getZero();
        if (ideal.stream().allMatch(m -> m.totalDegree == 1))
            // plain variables
            return uniRing.pow(uniRing.getOne().subtract(uniRing.variable(0)), ideal.size());

        // pick monomial
        DegreeVector pivotMonomial = ideal.stream().filter(m -> m.totalDegree > 1).findAny().get();
        int nVariables = pivotMonomial.exponents.length, var;
        for (var = 0; var < nVariables; ++var)
            if (pivotMonomial.exponents[var] != 0)
                break;
        final int variable = var;

        int[] varExponents = new int[nVariables];
        varExponents[variable] = 1;
        DegreeVector varMonomial = new DegreeVector(varExponents, 1);

        // sum J + <x_i>
        List<DegreeVector> sum = ideal.stream()
                .filter(m -> m.exponents[variable] == 0)
                .collect(Collectors.toList());
        sum.add(varMonomial);

        // quotient J : <x_i>
        List<DegreeVector> quot = ideal.stream()
                .map(m -> m.exponents[variable] > 0 ? m.dvDivideOrNull(variable, 1) : m)
                .collect(Collectors.toList());
        reduceMonomialIdeal(quot);

        return HilbertSeriesNumerator(sum).add(HilbertSeriesNumerator(quot).shiftRight(1));
    }

    /** Hilbert-Poincare series HPS(t) = P(t) / (1 - t)^m */
    public static final class HilbertSeries {
        private static final UnivariatePolynomial<Rational<BigInteger>> DENOMINATOR =
                UnivariatePolynomial.create(1, -1).mapCoefficients(Q, c -> new Rational<>(Z, c));
        /** Initial numerator (numerator and denominator may have nontrivial GCD) */
        public final UnivariatePolynomial<Rational<BigInteger>> initialNumerator;
        /** Initial denominator exponent (numerator and denominator may have nontrivial GCD) */
        public final int initialDenominatorDegree;
        /** Reduced numerator (GCD is cancelled) */
        public final UnivariatePolynomial<Rational<BigInteger>> numerator;
        /** Denominator exponent of reduced HPS(t) (that is ideal Krull dimension) */
        public final int denominatorExponent;

        private HilbertSeries(UnivariatePolynomial<Rational<BigInteger>> initialNumerator, int initialDenominatorDegree) {
            this.initialNumerator = initialNumerator;
            this.initialDenominatorDegree = initialDenominatorDegree;

            UnivariatePolynomial<Rational<BigInteger>> reducedNumerator = initialNumerator;
            int reducedDenominatorDegree = initialDenominatorDegree;
            while (true) {
                UnivariatePolynomial<Rational<BigInteger>> div = UnivariateDivision.divideOrNull(reducedNumerator, DENOMINATOR, true);
                if (div == null)
                    break;
                reducedNumerator = div;
                --reducedDenominatorDegree;
            }
            this.numerator = reducedNumerator;
            this.denominatorExponent = reducedDenominatorDegree;
        }

        /** The dimension of ideal */
        public int dimension() {
            return denominatorExponent;
        }

        /** Degree of ideal */
        private int idealDegree = -1;

        /** The degree of ideal */
        public synchronized int degree() {
            if (idealDegree == -1) {
                Rational<BigInteger> degree = numerator.evaluate(1);
                assert degree.isIntegral();
                idealDegree = degree.numerator.intValueExact();
            }
            return idealDegree;
        }

        /** Integral part I(t) of HPS(t): HPS(t) = I(t) + R(t)/(1-t)^m */
        private UnivariatePolynomial<Rational<BigInteger>> integralPart = null;
        /** Remainder part R(t) of HPS(t): HPS(t) = I(t) + R(t)/(1-t)^m */
        private UnivariatePolynomial<Rational<BigInteger>> remainderNumerator = null;

        /** Integral part I(t) of HPS(t): HPS(t) = I(t) + Q(t)/(1-t)^m */
        public UnivariatePolynomial<Rational<BigInteger>> integralPart() {
            computeIntegralAndRemainder();
            return integralPart;
        }

        /** Remainder part R(t) of HPS(t): HPS(t) = I(t) + R(t)/(1-t)^m */
        public UnivariatePolynomial<Rational<BigInteger>> remainderNumerator() {
            computeIntegralAndRemainder();
            return remainderNumerator;
        }

        private synchronized void computeIntegralAndRemainder() {
            if (integralPart == null) {
                UnivariatePolynomial<Rational<BigInteger>>[] divRem = UnivariateDivision.divideAndRemainder(numerator,
                        UnivariatePolynomialArithmetic.polyPow(DENOMINATOR, denominatorExponent, true), true);
                this.integralPart = divRem[0];
                this.remainderNumerator = divRem[1];
            }
        }

        /** Integral Hilbert polynomial (i.e. Hilbert polynomial multiplied by (dimension - 1)!) */
        private UnivariatePolynomial<Rational<BigInteger>> hilbertPolynomialZ = null;

        /** Integral Hilbert polynomial (i.e. Hilbert polynomial multiplied by (dimension - 1)!) */
        public synchronized UnivariatePolynomial<Rational<BigInteger>> hilbertPolynomialZ() {
            if (hilbertPolynomialZ == null) {
                hilbertPolynomialZ = UnivariatePolynomial.zero(Q);
                UnivariatePolynomial<Rational<BigInteger>> var = UnivariatePolynomial.one(Q).shiftRight(1);
                for (int i = 0; i <= numerator.degree(); ++i) {
                    UnivariatePolynomial<Rational<BigInteger>> term = UnivariatePolynomial.one(Q);
                    for (int j = 0; j < (denominatorExponent - 1); ++j)
                        term.multiply(var.clone().add(Q.valueOf(-i + 1 + j)));
                    term.multiply(numerator.get(i));
                    hilbertPolynomialZ.add(term);
                }
            }
            return hilbertPolynomialZ;
        }

        /** Hilbert polynomial */
        private UnivariatePolynomial<Rational<BigInteger>> hilbertPolynomial = null;

        /** Hilbert polynomial */
        public synchronized UnivariatePolynomial<Rational<BigInteger>> hilbertPolynomial() {
            if (hilbertPolynomial == null) {
                Rational<BigInteger> facCf = new Rational<>(Z, BigIntegerUtil.factorial(denominatorExponent - 1));
                hilbertPolynomial = hilbertPolynomialZ().clone().divideExact(facCf);
            }
            return hilbertPolynomial;
        }

        @Override
        public String toString() {
            return String.format("(%s) / (%s)^%s", numerator, DENOMINATOR, denominatorExponent);
        }
    }

    /* ************************************** Modular Groebner basis ********************************************** */


    public static List<MultivariatePolynomial<BigInteger>>
    ModularGB(List<MultivariatePolynomial<BigInteger>> ideal, Comparator<DegreeVector> monomialOrder) {
        // simplify generators as much as possible
        ideal = prepareGenerators(ideal, monomialOrder);
        if (ideal.size() == 1)
            return ideal;


        BigInteger basePrime = null;
        HilbertSeries baseSeries = null;
        List<MultivariatePolynomial<BigInteger>> baseBasis = null;

        PrimesIterator primes = new PrimesIterator(1L << 59);// start with a large enough prime
        List<MultivariatePolynomial<BigInteger>> previousGBCandidate = null;
        main:
        while (true) {
            // pick up next prime number
            long prime = primes.take();
            BigInteger bPrime = BigInteger.valueOf(prime);
            IntegersZp64 ring = Zp64(prime);
            IntegersZp bRing = ring.asGenericRing();

            // generators mod prime
            List<MultivariatePolynomialZp64> modGenerators =
                    ideal.stream().map(p -> MultivariatePolynomial.asOverZp64(p.setRing(bRing))).collect(Collectors.toList());

            // Groebner basis mod prime
            List<MultivariatePolynomialZp64> modBasis = GroebnerBasis(modGenerators, monomialOrder);
            // sort generators by increasing lead terms
            modBasis.sort((a, b) -> monomialOrder.compare(a.lt(), b.lt()));

            HilbertSeries modSeries = HilbertSeries(leadTermsIdeal(modBasis));

            // first iteration
            if (baseBasis == null) {
                baseBasis = modBasis.stream().map(MultivariatePolynomialZp64::toBigPoly).collect(Collectors.toList());
                basePrime = bPrime;
                baseSeries = modSeries;
                continue;
            }

            // check for Hilbert luckiness
            int c = ModHilbertSeriesComparator.compare(baseSeries, modSeries);
            if (c < 0)
                // current prime is unlucky
                continue;
            else if (c > 0) {
                // base prime was unlucky
                baseBasis = modBasis.stream().map(MultivariatePolynomialZp64::toBigPoly).collect(Collectors.toList());
                basePrime = bPrime;
                baseSeries = modSeries;
                continue;
            }

            // prime is Hilbert prime, so we compare monomial sets
            for (int i = 0, size = Math.min(baseBasis.size(), modBasis.size()); i < size; ++i) {
                c = monomialOrder.compare(baseBasis.get(i).lt(), modBasis.get(i).lt());
                if (c > 0)
                    // current prime is unlucky
                    continue main;
                else if (c < 0) {
                    // base prime was unlucky
                    baseBasis = modBasis.stream().map(MultivariatePolynomialZp64::toBigPoly).collect(Collectors.toList());
                    basePrime = bRing.modulus;
                    baseSeries = modSeries;
                    continue main;
                }
            }

            if (baseBasis.size() < modBasis.size()) {
                // base prime was unlucky
                baseBasis = modBasis.stream().map(MultivariatePolynomialZp64::toBigPoly).collect(Collectors.toList());
                basePrime = bRing.modulus;
                baseSeries = modSeries;
                continue;
            } else if (baseBasis.size() > modBasis.size())
                // current prime is unlucky
                continue;


            List<MultivariatePolynomial<BigInteger>> bModBasis = modBasis.stream().map(MultivariatePolynomialZp64::toBigPoly).collect(Collectors.toList());
            // prime is probably lucky, we can do Chinese Remainders
            for (int iGenerator = 0; iGenerator < baseBasis.size(); ++iGenerator) {
                MultivariatePolynomial<BigInteger> baseGenerator = baseBasis.get(iGenerator);
                PairedIterator<Monomial<BigInteger>, MultivariatePolynomial<BigInteger>> iterator
                        = new PairedIterator<>(baseGenerator, bModBasis.get(iGenerator));

                baseGenerator = baseGenerator.createZero();
                while (iterator.hasNext()) {
                    iterator.advance();

                    Monomial<BigInteger> baseTerm = iterator.aTerm;
                    BigInteger crt = ChineseRemainders.ChineseRemainders(basePrime, bPrime, baseTerm.coefficient, iterator.bTerm.coefficient);
                    baseGenerator.add(baseTerm.setCoefficient(crt));
                }

                baseBasis.set(iGenerator, baseGenerator);
            }

            basePrime = basePrime.multiply(bPrime);

            List<MultivariatePolynomial<Rational<BigInteger>>> gbCandidateFrac = new ArrayList<>();
            for (MultivariatePolynomial<BigInteger> gen : baseBasis) {
                MultivariatePolynomial<Rational<BigInteger>> gbGen = reconstructPoly(gen, basePrime);
                if (gbGen == null)
                    continue main;
                gbCandidateFrac.add(gbGen);
            }

            List<MultivariatePolynomial<BigInteger>> gbCandidate = toIntegral(gbCandidateFrac);
            if (gbCandidate.equals(previousGBCandidate) && isGroebnerBasis(ideal, gbCandidate, monomialOrder))
                return canonicalize(gbCandidate);
            previousGBCandidate = gbCandidate;
        }
    }

    @SuppressWarnings("unchecked")
    private static MultivariatePolynomial<Rational<BigInteger>> reconstructPoly(
            MultivariatePolynomial<BigInteger> base, BigInteger prime) {
        MultivariatePolynomial<Rational<BigInteger>> result = MultivariatePolynomial.zero(base.nVariables, Q, base.ordering);
        for (Monomial<BigInteger> term : base) {
            BigInteger[] numDen = RationalReconstruction.reconstructFareyErrorTolerant(term.coefficient, prime);
            if (numDen == null)
                return null;
            result.add(new Monomial<>(term, new Rational<>(Rings.Z, numDen[0], numDen[1])));
        }
        return result;
    }

    private static Comparator<HilbertSeries> ModHilbertSeriesComparator = (a, b) -> {
        UnivariatePolynomial<Rational<BigInteger>>
                aHilbert = a.hilbertPolynomial(),
                bHilbert = b.hilbertPolynomial();

        if (aHilbert.equals(bHilbert))
            return 0;

        for (int n = Math.max(a.numerator.degree(), b.numerator.degree()) + 1; ; ++n) {
            int c = aHilbert.evaluate(n).compareTo(bHilbert.evaluate(n));
            if (c != 0)
                return c;
        }
    };

    @SuppressWarnings("unchecked")
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> solveGB(List<Poly> generators,
                       List<Collection<DegreeVector>> gbSkeleton,
                       Comparator<DegreeVector> monomialOrder) {
        return solveGB0(generators, gbSkeleton.stream().map(c -> {
            TreeSet<DegreeVector> set = new TreeSet<>(monomialOrder);
            set.addAll(c);
            return set;
        }).collect(Collectors.toList()), monomialOrder);
    }

    static long SIMPLIFY = 0;
    static long SIMPLIFY_DEG_TAKE = 0;
    static long SIMPLIFY_EVALUATE = 0;
    static long PSIMPLIFY = 0;
    static long SYZYGY = 0;
    static long REDUCE = 0;
    static long REDUCE_REDUNDANT = 0;
    static long LINSOLVE = 0;
    static long REDUCE_AND_SOLVE = 0;
    static long SOLVE = 0;
    static long ADDEQ = 0;

    static void details() {
        System.out.println("SIMPLIFY         : " + TimeUnits.nanosecondsToString(SIMPLIFY));
        System.out.println("PSIMPLIFY        : " + TimeUnits.nanosecondsToString(PSIMPLIFY));
        System.out.println("SYZYGY           : " + TimeUnits.nanosecondsToString(SYZYGY));
        System.out.println("REDUCE AND SOLVE : " + TimeUnits.nanosecondsToString(REDUCE_AND_SOLVE));
        System.out.println("REDUCE           : " + TimeUnits.nanosecondsToString(REDUCE));
        System.out.println("REDUCE REDUNDANT : " + TimeUnits.nanosecondsToString(REDUCE_REDUNDANT));
        System.out.println("SOLVE            : " + TimeUnits.nanosecondsToString(SOLVE));
        System.out.println("LIN SOLVE        : " + TimeUnits.nanosecondsToString(LINSOLVE));
        System.out.println("ADDEQ            : " + TimeUnits.nanosecondsToString(ADDEQ));
    }


    /** when to drop unused variables */
    private static final int DROP_SOLVED_VARIABLES_THRESHOLD = 128;
    /** when to drop unused variables */
    private static final double DROP_SOLVED_VARIABLES_RELATIVE_THRESHOLD = 0.1;

    static int redundant = 0;

    @SuppressWarnings("unchecked")
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> solveGB0(List<Poly> generators,
                        List<SortedSet<DegreeVector>> gbSkeleton,
                        Comparator<DegreeVector> monomialOrder) {
        Poly factory = generators.get(0).createZero();
        if (!factory.isOverField()) {
            List gb = solveGB0(toFractions((List) generators), gbSkeleton, monomialOrder);
            if (gb == null)
                return null;
            return canonicalize((List<Poly>) toIntegral(gb));
        }

        // total number of unknowns
        int nUnknowns = gbSkeleton.stream().mapToInt(p -> p.size() - 1).sum();
        // we consider polynomials as R[u0, u1, ..., uM][x0, ..., xN], where u_i are unknowns
        // ring R[u0, u1, ..., uM]
        MultivariateRing<Poly> cfRing = Rings.MultivariateRing(factory.setNVariables(nUnknowns));
        // ring R[u0, u1, ..., uM][x0, ..., xN]
        MultivariateRing<MultivariatePolynomial<Poly>> pRing = Rings.MultivariateRing(factory.nVariables, cfRing, monomialOrder);

        AtomicInteger varCounter = new AtomicInteger(0);
        @SuppressWarnings("unchecked")
        MultivariatePolynomial<Poly>[] gbCandidate = gbSkeleton.stream().map(p -> {
            MultivariatePolynomial<Poly> head = pRing.create(p.last());
            MultivariatePolynomial<Poly> tail = p.headSet(p.last())
                    .stream()
                    .map(t -> pRing.create(t).multiply(cfRing.variable(varCounter.getAndIncrement())))
                    .reduce(pRing.getZero(), (a, b) -> a.add(b));
            return head.add(tail);
        }).toArray(MultivariatePolynomial[]::new);

        Term uTerm = factory.monomialAlgebra.getUnitTerm(nUnknowns);
        // initial ideal viewed as R[u0, u1, ..., uM][x0, ..., xN]
        List<MultivariatePolynomial<Poly>> initialIdeal
                = generators
                .stream().map(p -> pRing.factory().create(p.terms.values()
                        .stream().map(t -> new Monomial<>(t, cfRing.factory().create(uTerm.setCoefficientFrom(t))))
                        .collect(Collectors.toList())))
                .collect(Collectors.toList());

        long start;
        List<Equation<Term, Poly>> nonLinearEquations = new ArrayList<>();
        EquationSolver<Term, Poly> solver = createSolver(factory);
        TIntHashSet solvedVariables = new TIntHashSet();
        // reduce initial ideal to zero first (most simple)
        for (MultivariatePolynomial<Poly> idealElement : initialIdeal) {
            if (solvedVariables.size() == nUnknowns)
                // system is solved
                return gbSolution(factory, gbCandidate);

            start = System.nanoTime();
            SystemInfo result = reduceAndSolve(idealElement, gbCandidate, solver, nonLinearEquations);
            REDUCE_AND_SOLVE += System.nanoTime() - start;
            if (result == Inconsistent)
                return null;
            solvedVariables.addAll(solver.solvedVariables);

            start = System.nanoTime();
            // simplify GB candidate
            solver.simplifyGB(gbCandidate);
            // clear solutions (this gives some speed up)
            solver.clear();

            SIMPLIFY += System.nanoTime() - start;
        }

        System.out.println("Solved #1:" + solver.nSolved());

        // build set of all syzygies
        List<MultivariatePolynomial<Poly>> _tmp_gb_ = new ArrayList<>(initialIdeal);
        SyzygySet<Monomial<Poly>, MultivariatePolynomial<Poly>> sPairsSet = new SyzygyTreeSet<>(new TreeSet<>(defaultSelectionStrategy(monomialOrder)));
        Arrays.stream(gbCandidate).forEach(gb -> updateBasis(_tmp_gb_, sPairsSet, gb));
        // list of all non trivial S-pairs
        List<SyzygyPair<Monomial<Poly>, MultivariatePolynomial<Poly>>> sPairs = sPairsSet.allPairs();
        // start from the simplest ones
        sPairs.sort(Comparator.comparingInt(s -> s.j));

        int counter = 0;
        int aaaaa = 0;

        int[] nUnknownsGB = new int[gbCandidate.length];
        for (int i = 0; i < gbCandidate.length; ++i) {
            TIntHashSet unk = new TIntHashSet();
            for (Poly cf : gbCandidate[i].coefficients())
                unk.addAll(usedVars(cf));
            nUnknownsGB[i] = unk.size();
        }

        redundant = 0;
        for (SyzygyPair<Monomial<Poly>, MultivariatePolynomial<Poly>> sPair : sPairs) {
            if (solvedVariables.size() == nUnknowns)
                // system is solved
                return gbSolution(factory, gbCandidate);

            System.out.println("# sPairs           :   " + (++counter));
            System.out.println("# redundant sPairs :   " + redundant);
            System.out.println("# solved           :   " + (aaaaa + solvedVariables.size()));
            System.out.println("# linear           :   " + solver.nEquations());
            System.out.println("# non-linear       :   " + nonLinearEquations.size());
            System.out.println();
            details();
            System.out.println();
            System.out.println();

            start = System.nanoTime();
            MultivariatePolynomial<Poly> syzygy = syzygy(
                    sPair.syzygyGamma,
                    getFi(sPair.i, initialIdeal, gbCandidate),
                    getFi(sPair.j, initialIdeal, gbCandidate));
//            if (StreamSupport.stream(syzygy.coefficients().spliterator(), false).allMatch(IPolynomial::isConstant)
//                    && (sPair.i > initialIdeal.size() && nUnknownsGB[sPair.i - initialIdeal.size()] == 0)
//                    && (sPair.j > initialIdeal.size() && nUnknownsGB[sPair.j - initialIdeal.size()] == 0)) {
//                //
//
//                continue;
//            }

            SYZYGY += System.nanoTime() - start;

            start = System.nanoTime();
            SystemInfo result = reduceAndSolve(syzygy, gbCandidate, solver, nonLinearEquations);
            REDUCE_AND_SOLVE += System.nanoTime() - start;

            if (result == Inconsistent)
                return null;
            solvedVariables.addAll(solver.solvedVariables);

            start = System.nanoTime();
            if (solver.solvedVariables.size() > 0)
                // simplify GB candidate
                solver.simplifyGB(gbCandidate);
            for (int i = 0; i < gbCandidate.length; ++i) {
                TIntHashSet unk = new TIntHashSet();
                for (Poly cf : gbCandidate[i].coefficients())
                    unk.addAll(usedVars(cf));
                nUnknownsGB[i] = unk.size();
            }

            // clear solutions (this gives some speed up)
            solver.clear();
            SIMPLIFY += System.nanoTime() - start;


            if (solvedVariables.size() > DROP_SOLVED_VARIABLES_THRESHOLD
                    && 1.0 * solvedVariables.size() / nUnknowns >= DROP_SOLVED_VARIABLES_RELATIVE_THRESHOLD) {
                System.out.println("=== REDUCED === ------- === " + solvedVariables.size());
                dropSolvedVariables(solvedVariables, initialIdeal, gbCandidate, nonLinearEquations, solver);
                aaaaa += solvedVariables.size();
                nUnknowns -= solvedVariables.size();
                solvedVariables.clear(); ;
            }
        }

        if (solver.nSolved() == nUnknowns)
            // system is solved
            return gbSolution(factory, gbCandidate);

        return null;
    }

    static int[] usedVars(AMultivariatePolynomial equation) {
        int[] degrees = equation.degrees();
        TIntArrayList usedVars = new TIntArrayList();
        for (int i = 0; i < degrees.length; ++i)
            if (degrees[i] > 0)
                usedVars.add(i);
        return usedVars.toArray();
    }

    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    MultivariatePolynomial<Poly> getFi(int i,
                                       List<MultivariatePolynomial<Poly>> initialIdeal,
                                       MultivariatePolynomial<Poly>[] gbCandidate) {
        return i < initialIdeal.size() ? initialIdeal.get(i) : gbCandidate[i - initialIdeal.size()];
    }

    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    void dropSolvedVariables(
            TIntHashSet solvedVariables,
            List<MultivariatePolynomial<Poly>> initialIdeal,
            MultivariatePolynomial<Poly>[] gbCandidate,
            List<Equation<Term, Poly>> nonLinearEquations,
            EquationSolver<Term, Poly> solver) {
        if (solver.nSolved() != 0)
            throw new IllegalArgumentException();

        final int[] solved = solvedVariables.toArray();
        Arrays.sort(solved);

        MultivariateRing<Poly> oldPRing = ((MultivariateRing<Poly>) initialIdeal.get(0).ring);
        // new coefficient ring
        MultivariateRing<Poly> pRing = MultivariateRing(oldPRing.factory().dropVariables(solved));

        // transform initial ideal
        initialIdeal.replaceAll(p -> p.mapCoefficients(pRing, cf -> cf.dropVariables(solved)));
        // transform groebner basis
        Arrays.asList(gbCandidate).replaceAll(p -> p.mapCoefficients(pRing, cf -> cf.dropVariables(solved)));

        int[] vMapping = new int[oldPRing.nVariables()];
        int c = 0;
        for (int i = 0; i < vMapping.length; ++i) {
            if (Arrays.binarySearch(solved, i) >= 0)
                vMapping[i] = -1;
            else
                vMapping[i] = c++;
        }

        // transform non-linear
        nonLinearEquations.forEach(eq -> eq.dropVariables(vMapping));

        // transform linear
        solver.equations.forEach(eq -> eq.dropVariables(vMapping));
    }

    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    List<Poly> gbSolution(Poly factory, MultivariatePolynomial<Poly>[] gbCandidate) {
        List<Poly> result = new ArrayList<>();
        for (MultivariatePolynomial<Poly> gbElement : gbCandidate) {
            if (!gbElement.stream().allMatch(Poly::isConstant))
                return null;

            result.add(factory.create(gbElement.terms.values()
                    .stream()
                    .map(t -> t.coefficient.lt().setDegreeVector(t)).collect(Collectors.toList())));
        }
        return canonicalize(result);
    }

    /**
     * Builds & tries to solve system of equations obtained from a single reduction
     *
     * @param toReduce           generator (or S-pair) that should reduce to zero with GB candidate
     * @param gbCandidate        GB candidate
     * @param solver             solver
     * @param nonLinearEquations set of non-linear equations
     */
    static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    SystemInfo reduceAndSolve(MultivariatePolynomial<Poly> toReduce,
                              MultivariatePolynomial<Poly>[] gbCandidate,
                              EquationSolver<Term, Poly> solver,
                              List<Equation<Term, Poly>> nonLinearEquations) {
        long start;
        start = System.nanoTime();
        // reduce poly with GB candidate
        MultivariatePolynomial<Poly> remainder = MultivariateDivision.remainder(toReduce, gbCandidate);
        REDUCE += System.nanoTime() - start;

        if (remainder.isZero()) {
            REDUCE_REDUNDANT += System.nanoTime() - start;
            ++redundant;
            return Consistent;
        }

        // previous number of solved variables
        int nSolved = solver.solvedVariables.size();
        // whether some independent linear equations were generated
        boolean newLinearEqsObtained = false;
        for (Poly cf : remainder.coefficients()) {
            if (cf.isConstant())
                // equation is not solvable
                return Inconsistent;

            cf = solver.simplify(cf).monic();
            Equation<Term, Poly> eq = new Equation<>(cf);
            if (eq.isLinear) {
                // add equation
                boolean isNewEq = solver.addEquation(eq);
                if (isNewEq)
                    // equation is new (independent)
                    newLinearEqsObtained = true;
            } else if (!nonLinearEquations.contains(eq))
                nonLinearEquations.add(eq);
        }

        if (!newLinearEqsObtained)
            // nothing to do further
            return Consistent;

        if (solver.solvedVariables.size() > nSolved)
            // if some new solutions were already obtained we
            // can simplify non-linear equations so that
            // new linear combinations will be found
            updateNonLinear(solver, nonLinearEquations);

        while (true) {
            // try to find and solve some subset of linear equations
            SystemInfo result = solver.solve();

            if (result == Inconsistent)
                return Inconsistent;
            else if (result == UnderDetermined)
                return Consistent;

            // update non-linear equations with new solutions
            updateNonLinear(solver, nonLinearEquations);
            System.out.println("NEW BLOCK");
        }
    }

    private static <Term extends AMonomial<Term>, Poly extends AMultivariatePolynomial<Term, Poly>>
    void updateNonLinear(EquationSolver<Term, Poly> solver,
                         List<Equation<Term, Poly>> nonLinearEquations) {
        while (true) {
            boolean nlReduced = false;
            for (int i = nonLinearEquations.size() - 1; i >= 0; --i) {
                Equation<Term, Poly> eq = solver.simplify(nonLinearEquations.get(i));
                if (eq.reducedEquation.isZero())
                    nonLinearEquations.remove(i);
                else if (isLinear(eq.reducedEquation)) {
                    nlReduced = true;
                    solver.addEquation(eq);
                    nonLinearEquations.remove(i);
                } else
                    nonLinearEquations.set(i, eq);
            }
            if (!nlReduced)
                return;
        }
    }

    /** whether poly is linear */
    static boolean isLinear(AMultivariatePolynomial<? extends AMonomial, ?> poly) {
        return poly.terms.values().stream().allMatch(t -> t.totalDegree <= 1);
    }

    /** A single equation */
    private static class Equation<
            Term extends AMonomial<Term>,
            Poly extends AMultivariatePolynomial<Term, Poly>> {
        /** variables that present in this equation */
        final int[] usedVars;
        /** variable -> variable_in_reduced_equation */
        final TIntIntHashMap mapping;
        /** compact form of equation (with unused variables dropped) */
        final Poly reducedEquation;
        /** whether this equation is linear */
        final boolean isLinear;

        Equation(Poly equation) {
            int[] degrees = equation.degrees();
            TIntArrayList usedVars = new TIntArrayList();
            for (int i = 0; i < degrees.length; ++i)
                if (degrees[i] > 0)
                    usedVars.add(i);
            this.usedVars = usedVars.toArray();
            assert equation.isZero() || this.usedVars.length > 0;
            assert Arrays.stream(this.usedVars).allMatch(i -> i >= 0);
            assert isSorted(this.usedVars);
            this.reducedEquation = equation.dropSelectVariables(this.usedVars);
            this.mapping = new TIntIntHashMap(Constants.DEFAULT_CAPACITY, Constants.DEFAULT_LOAD_FACTOR, -1, -1);
            for (int i = 0; i < this.usedVars.length; ++i)
                mapping.put(this.usedVars[i], i);
            this.isLinear = isLinear(equation);
        }

        Equation(int[] usedVars, TIntIntHashMap mapping, Poly reducedEquation) {
            this.usedVars = usedVars;
            assert reducedEquation.isZero() || this.usedVars.length > 0;
            assert Arrays.stream(this.usedVars).allMatch(i -> i >= 0);
            assert isSorted(this.usedVars);
            this.mapping = mapping;
            this.reducedEquation = reducedEquation;
            this.isLinear = isLinear(reducedEquation);
        }

        void dropVariables(int[] vMapping) {
            for (int i = 0; i < usedVars.length; ++i)
                usedVars[i] = vMapping[usedVars[i]];
            assert isSorted(this.usedVars);
            assert Arrays.stream(this.usedVars).allMatch(i -> i >= 0);
            mapping.clear();
            for (int i = 0; i < this.usedVars.length; ++i)
                mapping.put(this.usedVars[i], i);
        }

        /** whether variable present in equation */
        boolean hasVariable(int variable) { return Arrays.binarySearch(usedVars, variable) >= 0;}

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Equation<?, ?> equation1 = (Equation<?, ?>) o;
            return Arrays.equals(usedVars, equation1.usedVars) && reducedEquation.equals(equation1.reducedEquation);
        }

        @Override
        public int hashCode() {
            int result = Arrays.hashCode(usedVars);
            result = 31 * result + reducedEquation.hashCode();
            return result;
        }
    }

    @SuppressWarnings("unchecked")
    static <Term extends AMonomial<Term>,
            Poly extends AMultivariatePolynomial<Term, Poly>>
    EquationSolver<Term, Poly> createSolver(Poly factory) {
        if (factory instanceof MultivariatePolynomial)
            return (EquationSolver<Term, Poly>) new EquationSolverE(((MultivariatePolynomial) factory).ring);
        else
            throw new RuntimeException();
    }


    /** solver */
    private static abstract class EquationSolver<
            Term extends AMonomial<Term>,
            Poly extends AMultivariatePolynomial<Term, Poly>> {
        /** list of linear equations */
        final List<Equation<Term, Poly>> equations = new ArrayList<>();
        /** variables solved so far */
        final TIntArrayList solvedVariables = new TIntArrayList();

        EquationSolver() {}

        /** number of equations */
        final int nEquations() {return equations.size();}

        /** add equation and return whether it was a new equation (true) or it is redundant (false) */
        abstract boolean addEquation(Equation<Term, Poly> eq);

        /** searches for a solvable block of equations and tries to solve it */
        abstract SystemInfo solve();

        /** simplifies given equation with solutions obtained so far */
        abstract Equation<Term, Poly> simplify(Equation<Term, Poly> eq);

        /** simplifies given poly with solutions obtained so far */
        abstract Poly simplify(Poly poly);

        /** clear all solutions */
        abstract void clear();

        /** simplifies GB element with solutions obtained so far */
        final MultivariatePolynomial<Poly> simplifyGB(MultivariatePolynomial<Poly> poly) {
            return poly.mapCoefficients(poly.ring, this::simplify);
        }

        /** simplifies GB with solutions obtained so far */
        final void simplifyGB(MultivariatePolynomial<Poly>[] gbCandidate) {
            for (int i = 0; i < gbCandidate.length; i++)
                gbCandidate[i] = simplifyGB(gbCandidate[i]);
        }

        final int nSolved() { return solvedVariables.size(); }
    }

    private static final class EquationSolverE<E>
            extends EquationSolver<Monomial<E>, MultivariatePolynomial<E>> {
        /** solutions obtained so far */
        private final List<E> solutions = new ArrayList<>();
        /** the ring */
        private final Ring<E> ring;

        EquationSolverE(Ring<E> ring) {
            this.ring = ring;
        }

        @Override
        void clear() {
            solvedVariables.clear();
            solutions.clear();
        }

        @Override
        boolean addEquation(Equation<Monomial<E>, MultivariatePolynomial<E>> equation) {
            long start = System.nanoTime();
            equation = simplify(equation);

            MultivariatePolynomial<E> eq = equation.reducedEquation;
            eq.monic();

            if (eq.isZero()) {
                ADDEQ += System.nanoTime() - start;
                // redundant equation
                return false;
            }
            if (equations.contains(equation)) {
                ADDEQ += System.nanoTime() - start;
                // redundant equation
                return false;
            }
            if (eq.nVariables == 1) {
                // equation can be solved directly
                Ring<E> ring = eq.ring;
                // solved variable
                int solvedVar = equation.usedVars[0];
                assert solvedVar >= 0;
                solvedVariables.add(solvedVar);
                solutions.add(ring.divideExact(ring.negate(eq.cc()), eq.lc()));

                // list of equations that can be updated
                List<Equation<Monomial<E>, MultivariatePolynomial<E>>> needUpdate = new ArrayList<>();
                for (int i = equations.size() - 1; i >= 0; --i) {
                    Equation<Monomial<E>, MultivariatePolynomial<E>> oldEq = equations.get(i);
                    if (!oldEq.hasVariable(solvedVar))
                        continue;
                    equations.remove(i);
                    needUpdate.add(oldEq);
                }
                needUpdate.forEach(this::addEquation);
                ADDEQ += System.nanoTime() - start;
                return true;
            }

            equations.add(equation);
            ADDEQ += System.nanoTime() - start;
            return true;
        }

        /** updates self with new solutions */
        private void selfUpdate() {
            List<Equation<Monomial<E>, MultivariatePolynomial<E>>> needUpdate = new ArrayList<>();
            for (int i = equations.size() - 1; i >= 0; --i) {
                Equation<Monomial<E>, MultivariatePolynomial<E>> oldEq = equations.get(i);
                Equation<Monomial<E>, MultivariatePolynomial<E>> newEq = simplify(oldEq);
                if (oldEq.equals(newEq))
                    continue;
                equations.remove(i);
                needUpdate.add(newEq);
            }
            needUpdate.forEach(this::addEquation);
        }

        @Override
        Equation<Monomial<E>, MultivariatePolynomial<E>> simplify(Equation<Monomial<E>, MultivariatePolynomial<E>> eq) {
            long start = System.nanoTime();
            // eliminated variables
            TIntArrayList eliminated = new TIntArrayList();
            // eliminated variables in eq.reducedEquation
            TIntHashSet rEliminated = new TIntHashSet();
            // reduced equation
            MultivariatePolynomial<E> rPoly = eq.reducedEquation;

            for (int i = 0; i < solutions.size(); ++i) {
                int var = solvedVariables.get(i);
                if (!eq.hasVariable(var))
                    continue;

                int rVar = eq.mapping.get(var);
                assert rVar >= 0;
                eliminated.add(var);
                rEliminated.add(rVar);
                rPoly = rPoly.evaluate(rVar, solutions.get(i));
            }
            if (eliminated.isEmpty()) {
                PSIMPLIFY += System.nanoTime() - start;
                return eq;
            }

            eliminated.sort();
            int[] eliminatedArray = eliminated.toArray();
            int[] usedVars = ArraysUtil.intSetDifference(eq.usedVars, eliminatedArray);
            TIntIntHashMap mapping = new TIntIntHashMap();
            for (int i = 0; i < usedVars.length; ++i)
                mapping.put(usedVars[i], i);

            PSIMPLIFY += System.nanoTime() - start;
            return new Equation<>(usedVars, mapping, rPoly.dropVariables(rEliminated.toArray()));
        }

        @Override
        MultivariatePolynomial<E> simplify(MultivariatePolynomial<E> poly) {
            int[] degs = poly.degrees();
            TIntArrayList subsVariables = new TIntArrayList();
            List<E> subsValues = new ArrayList<>();
            for (int i = 0; i < solvedVariables.size(); ++i)
                if (degs[solvedVariables.get(i)] > 0) {
                    subsVariables.add(solvedVariables.get(i));
                    subsValues.add(solutions.get(i));
                }
            if (subsVariables.isEmpty())
                return poly;

            return poly.evaluate(subsVariables.toArray(), subsValues.toArray(ring.createArray(subsValues.size())));
        }

        @Override
        SystemInfo solve() {
            long start = System.nanoTime();
            // sort equations from "simplest" to "hardest"
            equations.sort(Comparator.comparingInt(eq -> eq.usedVars.length));
            for (int i = 0; i < equations.size(); ++i) {
                // some base equation
                Equation<Monomial<E>, MultivariatePolynomial<E>> baseEq = equations.get(i);
                TIntHashSet baseVars = new TIntHashSet(baseEq.usedVars);

                // search equations compatible with base equation
                List<Equation<Monomial<E>, MultivariatePolynomial<E>>> block = new ArrayList<>(Collections.singletonList(baseEq));
                for (int j = 0; j < equations.size(); ++j) {
                    if (i == j)
                        continue;
                    Equation<Monomial<E>, MultivariatePolynomial<E>> jEq = equations.get(j);
                    if (jEq.usedVars.length > baseVars.size())
                        break;
                    if (baseVars.containsAll(jEq.usedVars))
                        block.add(jEq);
                }

                if (block.size() < baseVars.size())
                    // block can't be solved
                    continue;

                SystemInfo solve = solve(block, baseVars.toArray());
                if (solve == Inconsistent) {
                    SOLVE += System.nanoTime() - start;
                    return solve;
                }
                if (solve == UnderDetermined)
                    continue;

                equations.removeAll(block);
                selfUpdate();
                SOLVE += System.nanoTime() - start;
                return Consistent;
            }
            SOLVE += System.nanoTime() - start;
            return UnderDetermined;
        }

        /** solves a system of linear equations */
        SystemInfo solve(List<Equation<Monomial<E>, MultivariatePolynomial<E>>> equations, int[] usedVariables) {
            long start = System.nanoTime();

            int nUsedVariables = usedVariables.length;

            TIntIntHashMap mapping = new TIntIntHashMap();
            int[] linalgVariables = new int[nUsedVariables];
            int c = 0;
            for (int i : usedVariables) {
                mapping.put(i, c);
                assert i >= 0;
                linalgVariables[c] = i;
                ++c;
            }

            E[]
                    lhs[] = ring.createZeroesArray2d(equations.size(), nUsedVariables),
                    rhs = ring.createArray(equations.size());

            for (int i = 0; i < equations.size(); ++i) {
                Equation<Monomial<E>, MultivariatePolynomial<E>> eq = equations.get(i);
                rhs[i] = ring.negate(eq.reducedEquation.cc());
                for (Monomial<E> term : eq.reducedEquation) {
                    if (term.isZeroVector())
                        continue;
                    lhs[i][mapping.get(eq.usedVars[term.firstNonZeroVariable()])] = term.coefficient;
                }
            }

            E[] linalgSolution = ring.createArray(nUsedVariables);
            SystemInfo solve = LinearSolver.solve(ring, lhs, rhs, linalgSolution);
            if (solve == SystemInfo.Consistent) {
                this.solvedVariables.addAll(linalgVariables);
                this.solutions.addAll(Arrays.asList(linalgSolution));
            }
            LINSOLVE += System.nanoTime() - start;
            return solve;
        }
    }
}
