.. |br| raw:: html

   <br/>

.. |_| unicode:: 0xA0 
   :trim:

.. |____| replace:: |_|



========================================
Index of algorithms implemented in Rings
========================================



.. Univariate rings
.. ================

1. *Karatsuba multiplication* |____| (Sec. 8.1 in [GaGe03]_) |br| used with some adaptations for multiplication of univariate polynomials: 

 - `UnivariatePolynomial.multiply <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariatePolynomial.java>`_
 - `UnivariatePolynomialZp64.multiply <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariatePolynomialZp64.java>`_
	 
2. *Half-GCD and Extended Half-GCD* |____| (Sec. 11 in [GaGe03]_) |br| used (with adaptations inspired by [ShoNTL]_) for univariate GCD:

 - `UnivariateGCD.HalfGCD  <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateGCD.java>`_
 - `UnivariateGCD.ExtendedHalfGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateGCD.java>`_
 
3. *Subresultant polynomial remainder sequences* |____| ([GaLu03]_):

 - `UnivariateResultants <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateResultants.java>`_

4. *Modular resultant computation over* :math:`Z` *and* :math:`Q` *algebraic number fields* |____| ((Sec. 7.3 in [GeCL92]_):):

 - `UnivariateResultants <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateResultants.java>`_

5. *Modular GCD in* :math:`Z[x]` *and* :math:`Q[x]` |____| (Sec. 6.7 in [GaGe03]_, small primes version):

 - `UnivariateGCD.ModularGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateGCD.java>`_

6. *Modular GCD in* :math:`Q(\alpha)[x]` |____| ([LaMc89]_, [Enca95]_)

 - `UnivariateGCD.PolynomialGCDInNumberField <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateGCD.java>`_

7. *Fast univariate division with Newton iteration* |____| (Sec. 9.1 in [GaGe03]_) |br| used everywhere where multiple divisions (remainders) by the same divider are performed:

 - `UnivariateDivision.fastDivisionPreConditioning <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateDivision.java>`_
 - `UnivariateDivision.divideAndRemainderFast <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateDivision.java>`_
 
8. *Univariate square-free factorization in zero characteristic (Yun's algorithm)* |____| (Sec. 14.6 in [GaGe03]_):

 - `UnivariateSquareFreeFactorization.SquareFreeFactorizationYunZeroCharacteristics <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateSquareFreeFactorization.java>`_
     
9. *Univariate square-free factorization in non-zero characteristic (Musser's algorithm)* |____| (Sec. 8.3 in [GeCL92]_, [Muss71]_):

 - `UnivariateSquareFreeFactorization.SquareFreeFactorizationMusser <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateSquareFreeFactorization.java>`_
 - `UnivariateSquareFreeFactorization.SquareFreeFactorizationMusserZeroCharacteristics <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateSquareFreeFactorization.java>`_
 
10. *Distinct-degree factorization* |____| (Sec. 14.2 in [GaGe03]_) |br| plain version and adapted version with precomputed :math:`x`-powers (used by default):

 - `DistinctDegreeFactorization.DistinctDegreeFactorizationPlain <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/DistinctDegreeFactorization.java>`_
 - `DistinctDegreeFactorization.DistinctDegreeFactorizationPrecomputedExponents <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/DistinctDegreeFactorization.java>`_

11. *Shoup's baby-step giant-step algorithm for distinct-degree factorization* |____| ([Shou95]_) |br| used for factorization over fields with large cardinality:

 - `DistinctDegreeFactorization.DistinctDegreeFactorizationShoup <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/DistinctDegreeFactorization.java>`_

12. *Univariate modular composition* |br| plain algorithm with Horner schema:
 
 - `ModularComposition.compositionHorner <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/ModularComposition.java>`_

13. *Brent-Kung univariate modular composition* |____| ([BreK98]_, [Shou95]_):

 - `ModularComposition.compositionBrentKung <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/ModularComposition.java>`_

14. *Cantor-Zassenhaus algorithm (equal-degree splitting)* |____| (Sec. 14.3 in [GaGe03]_) |br| both for odd and even characteristic:

 - `EqualDegreeFactorization.CantorZassenhaus <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/EqualDegreeFactorization.java>`_

15. *Univaraite linear p-adic Hensel lifting* |____| (Sec. 6.5 in [GeCL92]_):

 - `univar.HenselLifting.createLinearLift <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/HenselLifting.java>`_
 - `univar.HenselLifting.liftFactorization <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/HenselLifting.java>`_

16. *Univaraite quadratic p-adic Hensel lifting* |____| (Sec. 15.4-15.5 in [GaGe03]_):

 - `univar.HenselLifting.createQuadraticLift <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/HenselLifting.java>`_
 - `univar.HenselLifting.liftFactorization <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/HenselLifting.java>`_

17. *Univariate polynomial factorization over finite fields* |br| uses Musser's square free factorization followed by distinct-degree factorization (either :math:`x`-powers or Shoup's algorithm) followed by Cantor-Zassenhaus equal-degree factorization:

 - `UnivariateFactorization.FactorInGF <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateFactorization.java>`_

18. *Univariate polynomial factorization over Z and Q* |br| uses factorization modulo small prime followed by Hensel lifting (adaptive linear/quadratic) and naive recombination:

 - `UnivariateFactorization.FactorInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateFactorization.java>`_
 - `UnivariateFactorization.FactorInQ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateFactorization.java>`_

19. *Univariate polynomial factorization over algebraic number fields* |br| uses Trager's algorithm [Trag76]_

 - `UnivariateFactorization.FactorInNumberField <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateFactorization.java>`_

20. *Univariate irreducibility test* |____| (Sec. 14.9 in [GaGe03]_):

 - `IrreduciblePolynomials.irreducibleQ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/IrreduciblePolynomials.java>`_

21. *Ben-Or's generation of irreducible polynomials* |____| (Sec. 14.9 in [GaGe03]_):

 - `IrreduciblePolynomials.randomIrreduciblePolynomial <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/IrreduciblePolynomials.java>`_

22. *Univariate polynomial interpolation* |br| Lagrange and Newton methods:

 - `UnivariateInterpolation <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/univar/UnivariateInterpolation.java>`_


.. Multivariate rings
.. ==================


23. *Brown multivariate GCD over finite fields* |____| ([Brow71]_, Sec. 7.4 in [GeCL92]_, [Yang09]_):

 - `MultivariateGCD.BrownGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

24. *Zippel's sparse GCD over finite fields* |____| ([Zipp79]_, [Zipp93]_, [dKMW05]_, [Yang09]_) |br| both for monic (with fast Vandermonde systems) and non-monic (LINZIP) cases:

 - `MultivariateGCD.ZippelGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

25. *Extended Zassenhaus GCD (EZ-GCD) over finite fields* |____| (Sec. 7.6 in [GeCL92]_, [MosY73]_):

 - `MultivariateGCD.EZGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

26. *Enhanced Extended Zassenhaus GCD (EEZ-GCD) over finite fields* |____| ([Wang80]_):

 - `MultivariateGCD.EEZGCD <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

27. *Modular multivariate GCD over Z with sparse interpolation* |____| ([Zipp79]_, [Zipp93]_, [dKMW05]_) |br| (the same interpolation techniques as in ``ZippelGCD`` is used):

 - `MultivariateGCD.ZippelGCDInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

28. *Modular multivariate GCD over Z (small primes version)*:

 - `MultivariateGCD.ModularGCDInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

29. *Kaltofen's & Monagan's generic modular multivariate GCD* |____| ([KalM99]_) |br| used for computing multivariate GCD over finite fields of very small cardinality:

 - `MultivariateGCD.ModularGCDInGF <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

30. *Kaltofen's & Monagan's generic modular multivariate GCD with EEZ-GCD for modular images* |____| ([KalM99]_) |br| used for computing multivariate GCD over finite fields of very small cardinality:

 -  `MultivariateGCD.KaltofenMonaganEEZModularGCDInGF <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

31. *Modular multivariate GCD over algebraic number fields with sparse interpolation* |____| |br| with either rational reconstruction [Enca95]_ or strict coefficient bounds [LaMc89]_ (the same interpolation techniques as in ``ZippelGCD`` is used [Zipp79]_, [Zipp93]_, [dKMW05]_):

 - `MultivariateGCD.ZippelGCDInNumberFieldViaRationalReconstruction <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_
 - `MultivariateGCD.ZippelGCDInNumberFieldViaLangemyrMcCallum <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_

32. *Modular multivariate GCD over algebraic number fields* |____| |br| with either rational reconstruction [Enca95]_ or strict coefficient bounds [LaMc89]_ (small primes version):

 - `MultivariateGCD.ZippelGCDInNumberFieldViaRationalReconstruction <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_
 - `MultivariateGCD.ModularGCDInNumberFieldViaLangemyrMcCallum <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateGCD.java>`_


33. *Brown multivariate resultant over finite fields* |____| |br| adaptation of Brown's algorithm ([Brow71]_, Sec. 7.4 in [GeCL92]_, [Yang09]_) for computing multivariate resultants:

 - `MultivariateResultants.BrownResultant <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateResultants.java>`_

34. *Zippel's sparse multivariate resultants over finite fields* |____| |br| adaptation of Zippel's sparse algorithm ([Zipp79]_, [Zipp93]_) for computing multivariate resultants:

 - `MultivariateResultants.ZippelResultant <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateResultants.java>`_

35. *Modular multivariate resultants over Z* |____| |br| modular algorithm for computing multivariate resultants over Z (uses Zippel's sparse interpolation techniques):

 - `MultivariateResultants.ModularResultantInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateResultants.java>`_

36. *Modular multivariate resultants over algebraic number fields* |____| |br| modular algorithm for computing multivariate resultants over algebraic number fields (uses Zippel's sparse interpolation techniques):

 - `MultivariateResultants.ModularResultantInNumberField <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateResultants.java>`_

37. *Multivariate square-free factorization in zero characteristic (Yun's algorithm)* |____| ([LeeM13]_):

 - `MultivariateSquareFreeFactorization.SquareFreeFactorizationYunZeroCharacteristics <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateSquareFreeFactorization.java>`_

38. *Multivariate square-free factorization in zero characteristic (Mussers's algorithm)* |____| ([Muss71]_, Sec. 8.3 in [GeCL92]_):

 - `MultivariateSquareFreeFactorization.SquareFreeFactorizationMusserZeroCharacteristics <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateSquareFreeFactorization.java>`_

39. *Multivariate square-free factorization in non-zero characteristic (Bernardins's algorithm)* |____| ([Bern99]_):

 - `MultivariateSquareFreeFactorization.SquareFreeFactorizationBernardin <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateSquareFreeFactorization.java>`_

40. *Bernardin's fast dense multivariate Hensel lifting* |____| ([Bern99]_, [LeeM13]_) |br| both for bivariate case (original Bernardin's paper) and multivariate case (Lee thesis) and both with and without precomputed leading coefficients:

 - `multivar.HenselLifting <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/HenselLifting.java>`_

41. *Sparse Hensel lifting* |____| ([Kalt85]_, [LeeM13]_)

 - `multivar.HenselLifting <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/HenselLifting.java>`_

42. *Fast dense bivariate factorization with recombination* |____| ([Bern99]_, [LeeM13]_):

 - `MultivariateFactorization.bivariateDenseFactorSquareFreeInGF <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateFactorization.java>`_
 - `MultivariateFactorization.bivariateDenseFactorSquareFreeInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateFactorization.java>`_

43. *Kaltofen's multivariate factorization in finite fields* |____| ([Kalt85]_, [LeeM13]_) |br| modified version of original Kaltofen's algorithm for leading coefficient precomputation with square-free decomposition (instead of distinct variables decomposition) due to Lee is used; further adaptations are made to work in finite fields of very small cardinality; the resulting algorithm is close to [LeeM13]_, but at the same time has many differences in details:

 - `MultivariateFactorization.factorInGF <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateFactorization.java>`_

44. *Kaltofen's multivariate factorization Z* |____| ([Kalt85]_, [LeeM13]_) |br| (with the same modifications as for algorithm for finite fields):

 - `MultivariateFactorization.factorInZ <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateFactorization.java>`_

45. *Multivariate polynomial factorization over algebraic number fields* |br| uses Trager's algorithm [Trag76]_

 - `MultivariateFactorization.FactorInNumberField <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateFactorization.java>`_

46. *Multivariate polynomial interpolation with Newton method*:

 - `MultivariateInterpolation <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/MultivariateInterpolation.java>`_

47. *Primitive elements of multiple field extensions* |____| ([Trag76]_, [Yoko89]_):

 - `MultipleFieldExtension <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/MultipleFieldExtension.java>`_
 
48. *Construction of splitting fields* |____| ([Trag76]_, [Yoko89]_):

 - `MultipleFieldExtension <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/MultipleFieldExtension.java>`_

 
49. *Buchberger algorihm for Groebner basis* |____| ([Buch76]_, [BecW93]_, [CLOS97]_) |br| with Gebauer-Moller installation of Buchberger criteria ([GebM88]_, [BecW93]_) and sugar strategy for lexicographic orders ([GMNR88]_):

 - `GroebnerBases.BuchbergerGB <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/GroebnerBases.java>`_

50. *Faugere's F4 algorithm for Groebner basis* |____| ([Faug99]_) |br| with fast sparse linear algebra [FauL10]_ and simplification algoritm from [JouV11]_:

 - `GroebnerBases.F4GB <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/GroebnerBases.java>`_

51. *Hilbert-Poincare series and Hilbert-driven methods for Groebner bases* |____| ([Trav96]_):

 - `GroebnerBases.HilbertGB <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/GroebnerBases.java>`_

52. *Modular Groebner bases in Z* |____| ([Arno03]_):

 - `GroebnerBases.ModularGB <https://github.com/PoslavskySV/rings/tree/develop/rings/src/main/java/cc/redberry/rings/poly/multivar/GroebnerBases.java>`_



References
==========

.. [GaGe03] J von zur Gathen and J Gerhard. Modern computer algebra (2 ed.). Cambridge University Press, 2003.

.. [ShoNTL] V Shoup. NTL: A library for doing number theory. www.shoup.net/ntl

.. [GeCL92] K O Geddes, S R Czapor, G Labahn. Algorithms for Computer Algebra. 1992.

.. [Muss71] D R Musser. Algorithms for polynomial factorization, Ph.D. Thesis, University of Wisconsin, 1971.

.. [Shou95] V Shoup. A new polynomial factorization algorithm and its implementation. J. Symb. Comput., 20(4):363–397, 1995.

.. [BreK98] R P Brent and H T Kung. Fast algorithms for manipulating formal power series. J. Assoc. Comput. Math. 25:581-595, 1978

.. [Brow71] W S Brown. On Euclid's algorithm and the computation of polynomial greatest common divisors. J. ACM, 18(4):478–504, 1971.

.. [Enca95] M J Encarnacion, Computing GCDs of Polynomials over Algebraic Number Fields, J. Symbolic Computation 20, pp. 299–313, 1995.

.. [LaMc89] L Langemyr, S McCallum, The Computation of Polynomial Greatest Common Divisors Over an Algebraic Number Field, J. Symbolic Computation (1989) 8, 429-448, 1989

.. [GaLu03] J von zur Gathen and T Lu􏱧cking, Subresultants revisited, Theoretical Computer Science 297 (2003) 199–239

.. [Trag76] B M Trager, Algebraic Factoring and Rational Function Integration, Proc. SYMSAC 76 

.. [Zipp79] R E Zippel. Probabilistic algorithms for sparse polynomials. In Proceedings of the International Symposiumon on Symbolic and Algebraic Computation, EUROSAM '79, pages 216–226, London, UK, UK, 1979. Springer-Verlag.

.. [Zipp93] R E Zippel. Effective Polynomial Computation. Kluwer International Series in Engineering and Computer Science. Kluwer Academic Publishers, 1993.

.. [dKMW05] J de Kleine, M B Monagan, A D Wittkopf. Algorithms for the Non-monic Case of the Sparse Modular GCD Algorithm. Proceeding of ISSAC '05, ACM Press, pp. 124-131 , 2005.

.. [Yang09] S Yang. Computing the greatest common divisor of multivariate polynomials over finite fields. Master's thesis, Simon Fraser University, 2009.

.. [MosY73] J Moses and D Y Y Yun, "The EZGCD Algorithm" pp. 159-166 in Proc. ACM Annual Conference, (1973).

.. [Wang80] P S Wang, "The EEZ-GCD Algorithm," ACM SIGSAMBull., 14 pp. 50-60 (1980).

.. [KalM99] E Kaltofen, M. B. Monagan. On the Genericity of the Modular Polynomial GCD Algorithm. Proceeding of ISSAC '99, ACM Press, 59-66, 1999.

.. [Bern99] L Bernardin. Factorization of Multivariate Polynomials over Finite Fields. PhD thesis, ETH Zu ̈rich, 1999.

.. [LeeM13] M M-D Lee, Factorization of multivariate polynomials,  Ph.D. thesis, University of Kaiserslautern, 2013

.. [Kalt85] E Kaltofen. Sparse Hensel lifting. In EUROCAL 85 European Conf. Comput. Algebra Proc. Vol. 2, pages 4–17, 1985.

.. [Yoko89] K Yokoyama, Computing Primitive Elements of Extension Fields, J. Symbolic Computation (1989) 8, 553-580

.. [Trav96] C Traverso, Hilbert Functions and the Buchberger Algorithm, J. Symbolic Comp., 22(4):355--376, 1996.

.. [Faug99] J-C Faugere, A new efficient algorithm for computing Gröbner bases (F4), Journal of Pure and Applied Algebra. Elsevier Science. 139 (1): 61–88, 1999

.. [FauL10] J-C Faugere, S Lachartre, Parallel Gaussian elimination for Gröbner bases computations in finite fields, PASCO (2010)

.. [JouV11] A Joux, V Vitse, A Variant of the F4 Algorithm. In: Kiayias A. (eds) Topics in Cryptology – CT-RSA 2011. CT-RSA 2011. Lecture Notes in Computer Science, vol 6558. Springer, Berlin, Heidelberg

.. [Buch76] B Buchberger, Theoretical Basis for the Reduction of Polynomials to Canonical Forms, ACM SIGSAM Bulletin. ACM. 10 (3): 19–29

.. [GebM88] R Gebauer and H Moller, On an Installation of Buchberger's Algorithm, Journal of Symbolic Computation, 6(2 and 3):275–286, October/December 1988

.. [GMNR88] A Giovini, T Mora, G Niesi, L Robbiano and C Traverso, One sugar cube, please, or Selection strategies in the Buchberger Algorithm. In S. M. Watt, editor, Proceedings of the 1991 International Symposium on Symbolic and Algebraic Computation. ISSAC'91, ACM Press, 1991.

.. [BecW93] T Becker and V Weispfenning, Groebner Bases, a Computationnal Approach to Commutative Algebra. Graduate Texts in Mathematics. Springer-Verlag, 1993.

.. [CLOS97] D Cox, J Little and D O'Shea, Ideals, Varieties, and Algorithms: An Introduction to Computational Algebraic Geometry and Commutative Algebra, Springer, 1997

.. [Arno03] E Arnold, Modular algorithms for computing Gröbner bases, Journal of Symbolic Computation Vol. 35, Issue 4, April 2003, Pages 403-419





