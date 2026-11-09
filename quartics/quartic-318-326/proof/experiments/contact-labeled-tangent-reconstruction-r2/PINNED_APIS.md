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


## Original valuations, residue rings and poles

Exact same Mathlib pin56a005855ea17e0b0958f73ec801ae140b0a1679.
Mathlib/RingTheory/Valuation/ValuationRing.lean lines374–376:
ValuationRing.isInteger_or_isInteger R x proves x or x^-1 is the image of an
ACTUAL element of R inside the specified original fraction field. Its proof
uses original fraction representation and total divisibility. The local pole
argument uses precisely this theorem, not an assumed holomorphic representative.

Mathlib/RingTheory/Valuation/Basic.lean lines1170,1269–1274:
AddValuation.map_pow is n times the additive value; map_inv negates it;
map_div subtracts values. These exact directions retain index1/index2 and the
factor2 from the ORIGINAL quadratic equation, including negative pole orders.

Mathlib/Algebra/Ring/Parity.lean lines398–401:
neg_one_pow_eq_one_iff_even requires (-1)≠1 in the ACTUAL residue field. The
consumer supplies CharZero of the full residue field, not an identification
with Q or a selected rational point.

Mathlib/RingTheory/Multiplicity.lean:
FiniteMultiplicity.of_prime_left, emultiplicity_eq_multiplicity and
multiplicity_pos_of_dvd have actual prime/nonzero hypotheses. The accepted
LinearContactSquareclass.product_squarefree proves the old complementary
cubic is squarefree, and squarefree_iff_emultiplicity_le_one then bounds every
prime multiplicity by1. No degree1 restriction is placed on the tested prime.

The exact accepted FractionSqrtTwo318 prime valuation extension argument was
read as a proof source. Only its generic multiplicity/additive-valuation
extension steps are adapted; its specialized arithmetic field, real places
and square/unit conclusions are not imported or used.


## Actual tame local action and original fraction field

Same Mathlib pin56a005855ea17e0b0958f73ec801ae140b0a1679.
Read Mathlib/RingTheory/DiscreteValuationRing/Basic.lean actual declarations:
exists_irreducible R constructs an actual uniformizer; associated_of_irreducible
R has R EXPLICIT and relates actual irreducibles; irreducible_iff_uniformizer
identifies the ORIGINAL maximal ideal with its actual principal ideal;
eq_unit_mul_pow_irreducible decomposes each nonzero original element.

Read Mathlib/Algebra/Group/Irreducible/Lemmas.lean: MulEquiv.irreducible_iff
applies to any MulEquivClass, including the actual ring equivalence. Read
Mathlib/Algebra/GroupWithZero/Associated.lean: Associated p q is an ACTUAL
unit u with p*u=q; Associated.irreducible transfers irreducibility; its
actual dvd_iff_dvd_left retains the same divisibility relation.

Read Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean:
residue_eq_zero_iff is original maximal-ideal membership and
residue_ne_zero_iff_isUnit detects units in the SAME local ring. The residue
identity in the model applies to all elements of that ring, including the
original uniformizer multiplier and original leading coefficients.

Read Mathlib/RingTheory/Localization/FractionRing.lean: div_surjective A z
produces ACTUAL a,b in A with b a non-zero-divisor and map(a)/map(b)=z in the
specified original fraction field. This proves triviality of a field action
from its actual local restriction; it is not a dimension-only comparison.

Read Mathlib/Algebra/BigOperators/Associated.lean: Prime.dvd_finsetProd_iff
has the actual Finset and factor function, returning an actual factor divisor.
Read Mathlib/Algebra/Polynomial/Div.lean: dvd_iff_isRoot computes divisibility
by the original X-C(contact) through evaluation at that exact contact.
Original source contacts/cubic/complement definitions and their distinctness
are byte-identical accepted producers retained through the18-source closure.

Exact same pin, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean:
map_div₀ (f:F)(a b:G0) : f(a/b)=f(a)/f(b), with GroupWithZero on
source/target and MonoidWithZeroHomClass F G0 G0'. This is the actual
applicable declaration for the original field AlgEquiv/AlgHom/RatFunc.C maps.
The generic group map_div did not rewrite the original field map in hosted776.
