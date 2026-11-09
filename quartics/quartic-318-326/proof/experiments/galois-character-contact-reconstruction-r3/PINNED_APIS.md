# Primary APIs read at the exact Mathlib pin

Pin56a005855ea17e0b0958f73ec801ae140b0a1679.

Mathlib/RingTheory/TensorProduct/Maps.lean lines147–169:
Algebra.TensorProduct.lift requires the two actual algebra maps and commuting
images; lift_tmul computes their product. The candidate target is commutative,
so Commute.all supplies precisely that premise.
Mathlib/RingTheory/TensorProduct/Basic.lean, Algebra.TensorProduct.ext:
equality is checked on the original includeLeft/includeRight maps, recursively
through both original tensor pairs, then AdjoinRoot.algHom_ext on each root.

Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:
LinearEquiv.ofInjectiveOfFinrankEq upgrades the GIVEN injective linear map,
requires target finite-dimensional and exact finrank equality, and has that
same map as its toLinearMap by rfl. Here the actual root evaluation is injective
because the original tensor algebra is proved a field; original degree16 and
the supplied degree of L give the equality. Its surjectivity is passed to
AlgEquiv.ofBijective for the SAME original algebra homomorphism.

Mathlib/FieldTheory/RatFunc/Basic.lean lines973–1000:
num_div_denom is the exact original rational function; isCoprime_num_denom
supplies coprimality; num_ne_zero and denom_ne_zero provide actual nonzero
polynomials. No arbitrary chosen fraction or abstract divisor substitutes for
these canonical numerator and denominator functions.

Mathlib/Algebra/Polynomial/FieldDivision.lean:
degree_eq_zero_of_isUnit and eq_C_of_degree_le_zero identify a polynomial unit
with its coefficient0 over the original field. The square-factor construction
is adapted from the actual read proof of accepted SquareFactorization318,
using normalizedFactors, multiplicity_eq_count_normalizedFactors,
normalize_normalized_factor, prod_normalizedFactors and the finite product
count reconstruction. Its arithmetic-specific positivity step is NOT imported
or asserted; the residual arbitrary nonzero field scalar is retained.


## Genuine Galois normal basis and fixed base

Exact same Mathlib pin56a005855ea17e0b0958f73ec801ae140b0a1679.
Mathlib/FieldTheory/Galois/NormalBasis.lean lines119–129:
IsGalois.normalBasis F L : Module.Basis (L ≃ₐ[F] L) F L for an ACTUAL finite
Galois extension; normalBasis_apply e states b(e)=e(b(1)). The proof is the
actual normal basis theorem, not an assumed character eigenbasis. The current
Fourier sum uses this exact basis, and its repr at identity proves nonzero.

Mathlib/FieldTheory/Galois/Basic.lean lines351–360:
IsGalois.mem_range_algebraMap_iff_fixed x identifies membership in the ORIGINAL
algebraMap range with being fixed by ALL original field automorphisms. This
exact theorem descends the square of the constructed character vector.
The same file lines107–111 has IsGalois.card_aut_eq_finrank: Nat.card of actual
automorphisms equals actual extension finrank under finite Galois hypotheses.
The specified isomorphism to the concrete sixteen-element binary group gives
actual degree16; the degree is not separately presumed by the consumer.

The exact old FourRootAutomorphisms generator/sign maps remain the destination
of the reconstructed equivariance statement. ComplementaryFunctionRigidity
uses full original functions and explicit base-field nonzero scales, never
merely names of subfields, matching dimensions, or equality of squares.
