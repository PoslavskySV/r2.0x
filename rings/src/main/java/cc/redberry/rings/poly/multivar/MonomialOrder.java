package cc.redberry.rings.poly.multivar;

import java.io.Serializable;
import java.util.Comparator;

/**
 * Common monomial orderings.
 *
 * @since 1.0
 */
public final class MonomialOrder {
    private MonomialOrder() { }

    /**
     * Lexicographic monomial order.
     */
    public static final Comparator<DegreeVector> LEX = (Comparator<DegreeVector> & Serializable)
            (DegreeVector a, DegreeVector b) -> {
                for (int i = 0; i < a.exponents.length; ++i) {
                    int c = Integer.compare(a.exponents[i], b.exponents[i]);
                    if (c != 0)
                        return c;
                }
                return 0;
            };
    /**
     * Graded lexicographic monomial order.
     */
    public static final Comparator<DegreeVector> GRLEX = (Comparator<DegreeVector> & Serializable)
            (DegreeVector a, DegreeVector b) -> {
                int c = Integer.compare(a.totalDegree, b.totalDegree);
                return c != 0 ? c : LEX.compare(a, b);
            };
    /**
     * Antilexicographic monomial order.
     */
    public static final Comparator<DegreeVector> ALEX = (Comparator<DegreeVector> & Serializable)
            (DegreeVector a, DegreeVector b) -> LEX.compare(b, a);
    /**
     * Graded reverse lexicographic monomial order
     */
    public static final Comparator<DegreeVector> GREVLEX = (Comparator<DegreeVector> & Serializable)
            (Comparator<DegreeVector> & Serializable) (DegreeVector a, DegreeVector b) -> {
                int c = Integer.compare(a.totalDegree, b.totalDegree);
                if (c != 0)
                    return c;
                for (int i = a.exponents.length - 1; i >= 0; --i) {
                    c = Integer.compare(b.exponents[i], a.exponents[i]);
                    if (c != 0)
                        return c;
                }
                return 0;
            };

    /**
     * Block product of orderings
     */
    public static Comparator<DegreeVector> product(Comparator<DegreeVector> orderings[], int[] nVariables) {
        return new ProductOrdering(orderings, nVariables);
    }

    /**
     * Block product of orderings
     */
    @SuppressWarnings("unchecked")
    public static Comparator<DegreeVector> product(Comparator<DegreeVector> a, int anVariables, Comparator<DegreeVector> b, int bnVariable) {
        return new ProductOrdering(new Comparator[]{a, b}, new int[]{anVariables, bnVariable});
    }

    static final class ProductOrdering implements Comparator<DegreeVector>, Serializable {
        final Comparator<DegreeVector> orderings[];
        final int[] nVariables;

        ProductOrdering(Comparator<DegreeVector>[] orderings, int[] nVariables) {
            this.orderings = orderings;
            this.nVariables = nVariables;
        }

        @Override
        public int compare(DegreeVector a, DegreeVector b) {
            int prev = 0;
            for (int i = 0; i < nVariables.length; i++) {
                // for each block
                DegreeVector
                        aBlock = a.range(prev, prev + nVariables[i]),
                        bBlock = b.range(prev, prev + nVariables[i]);

                int c = orderings[i].compare(aBlock, bBlock);
                if (c != 0)
                    return c;

                prev += nVariables[i];
            }
            return 0;
        }
    }
}
