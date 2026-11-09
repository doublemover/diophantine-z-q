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


## Actual scheme normalization and original generic stalks

Read full required declarations at the same Mathlib pin
56a005855ea17e0b0958f73ec801ae140b0a1679.
Mathlib/AlgebraicGeometry/Normalization.lean, UniversalProperty:
normalizationDesc f f1 f2 (H:f=f1>>f2) requires qcqs f and integral f2;
toNormalization_normalizationDesc and normalizationDesc_comp are the exact
source/base equations. normalization.hom_ext requires only affine target
structure and BOTH original source/base equations. The actual normalization
has an integral fromNormalization, dominant toNormalization, and is integral
when the original source is integral. These are the actual scheme objects,
not chart collections or abstract normality records.

Mathlib/AlgebraicGeometry/FunctionField.lean: actual affine coefficient
algebra is StructureSheaf.toStalk; functionField_isFractionRing_of_affine
uses the ORIGINAL generic prime (proved to be0) and original localization.
Both R and K affine generic stalks use exactly this instance. Actual
AffineFunctionFieldMap318.on_coefficient was read to verify naturality of
the SAME dominant generic-stalk map, not just existence of a field equivalence.

Mathlib/RingTheory/Localization/FractionRing.lean div_surjective gives
actual numerator/denominator witnesses for every original field element.
Both uses in AffineFractionGeneric318 preserve those coefficient maps.
Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean map_div0 (Unicode subscript0)
is used for the original field RingHom/AlgEquiv maps, not group-only map_div.

Mathlib/AlgebraicGeometry/Noetherian.lean: an actual open immersion into a
locally Noetherian target is quasi-compact. Contact's existing actual normal
model is Noetherian by ContactGlobalNormal318.noetherian_model. Its whole
sourceOpen is used, not a smaller ad hoc open. Spec of a field has finite
underlying space, giving quasi-compactness of the candidate generic base map;
quasi-separatedness follows from its actual affine-map/open-chart factorization.

Accepted IntegralGenericIso318.app_isIso/restrict_isIso was read in full:
requires ACTUAL integral dominant f and isomorphism of its ACTUAL generic
stalk map, plus a nonempty entire normal affine target open. It proves original
app bijective by integral/fraction comparison. NormalizationBirationalComparison
supplies these exact inputs, with nonemptiness witnessed by the current point.

Accepted SourceOpenFractionField318.open_fractionField and
openEmbedding_on_polynomial retain the original whole localized order and its
original Kummer field embedding. ContactGlobalNormal318.sourceCover and
chart_properties retain the literal original affine normalization opens.
ContactGlobalSigns318.on_open/over_line and
SourceSignFieldComparison318.open_embedding were read to verify the EXACT
old scheme action and original-field sign under that same open embedding.
SchematicEqualityExtension318.ext requires the actual base square, separated
target structure and a schematically dominant comparison map; reducedness of
the actual integral Y promotes its actual dominant generic g accordingly.


## Original center and full valuation restriction

Same pinned Mathlib revision56a005855ea17e0b0958f73ec801ae140b0a1679.
Read RingTheory/Multiplicity.lean actual declaration:
FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd (hfin:FiniteMultiplicity a b)
returns c with b=a^(multiplicity a b)*c and not a divides c. The original
polynomial prime and original nonzero polynomial provide hfin; no unit factor
or all-field valuation identity is assumed.

Read DiscreteValuationRing/Basic.lean addVal_eq_zero_iff: canonical addVal
vanishes precisely on actual units. Original residue_ne_zero_iff_isUnit detects
those units from the supplied actual center map. The already constructed
DVRFractionCharacterParity.value_integral fixes the valuation extension to the
SAME original fraction field. PolynomialPrimeValuation.primePlace_order fixes
its comparison with canonical original RatFunc numerator/denominator orders.

The coefficient square includes the original algebraMap Q(t)->L and the
original Q[t]->Q(t), not a separately chosen rational-function embedding.
Field map division uses pinned map_div0 (Unicode subscript0); the valuation's
own .map_div is its additive valuation subtraction identity. The factors1/2
are actual canonical prime orders; no scalar is discarded in the derived law.


## Actual prime localization and affine inertia

Pinned Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 primary sources read:
- RingTheory/Localization/Defs.lean: IsLocalization.lift takes actual units
  of every denominator; lift_eq fixes the SAME original coefficient map;
  ringHom_ext compares restrictions along that algebraMap.
- RingTheory/Localization/LocalizationLocalization.lean:
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S T requires
  original base domain, actual localization and original fraction ring T,
  plus the explicit scalar tower, and returns IsFractionRing S T.
- RingTheory/Localization/AtPrime/Basic.lean:
  to_map_mem_maximal_iff S P x identifies actual localization maximal-ideal
  membership with x in the original P. The actual localization is a local
  domain; no substitute local ring is introduced.
- RingTheory/DiscreteValuationRing/Basic.lean:
  irreducible_of_span_eq_maximalIdeal x hx h consumes maximalIdeal=span{x};
  addVal_uniformizer and Irreducible.addVal_pow give the exact canonical
  values1/2. addVal_eq_zero_of_unit removes only the stated actual unit.

Accepted original HeightOneDVR318.localization was read in full: normal
Noetherian domain and actual prime height1 produce DVR on the literal
Localization.AtPrime. PrimeLocalizationInertia318 was read in full:
primeCompl_map, lift and lift_algebraMap retain the given affine automorphism;
residue_trivial_iff extends the original modulo-prime identity to all local
fractions. Exact accepted source hashes are in COPY_BINDINGS.json.

The residue characteristic proof constructs the literal ring hom Q into the
actual residue field using original coefficients, then uses field-hom
injectivity to reflect equality of natural casts. No residue-field algebra
instance or characteristic-zero premise is supplied by the consumer.


## Full inertia to canonical order: primary theorem hypotheses read

All pins use Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.

RingTheory/DiscreteValuationRing/Basic.lean: eq_unit_mul_pow_irreducible gives
x=u*pi^n; length_quotient_pow_maximalIdeal gives length R(R/m^n)=n;
addVal_uniformizer and addVal_pow use the SAME canonical normalization.
RingTheory/RamificationInertia/Ramification.lean: ramificationIdx is exactly
(Module.length B_P (B_P/(P.under A).map(algebraMap A B_P))).toNat for prime P.
The original contracted polynomial ideal is mapped to the literal span of
its original image. Nonzero image proves addVal is not top, justifying the
ENat.toNat round trip; no finite-length assumption is silently dropped.

NumberTheory/RamificationInertia/Galois.lean:
card_inertia_eq_ramificationIdxIn requires domain R/S, actual module-finite
and flat extension, finite group with MulSemiringAction/IsGaloisGroup, actual
prime P lying over p, both primes, and HasSeparableResidueFieldsAt R S p.
ramificationIdxIn_eq_ramificationIdx identifies the index at that SAME P.
Every one of these inputs is constructed for the original normal closure.

RingTheory/DedekindDomain/IntegralClosure.lean: IsIntegralClosure.finite,
module_free, isDedekindDomain and isFractionRing_of_finite_extension consume
actual base fraction field Q(t), actual finite separable L, original scalar
towers, and literal integral closure. Polynomial Q is a PID and normal
Noetherian domain; torsion-free field action supplies module_free/flat.
RingTheory/IsGaloisGroup/Basic.lean: of_isFractionRing requires original
compatible actions through SMulDistribClass, actual integral extension and
integrally closed base; it transfers the SAME field Galois group predicate.
RingTheory/Invariant/Galois.lean constructs the actual integral-closure
MulSemiringAction and its compatible generic action. IntegralRestrict.lean
pins galRestrict and algebraMap_galRestrict_apply, in the exact direction
map_B_L(galRestrict(sigma)(b))=sigma(map_B_L(b)).

RingTheory/LocalRing/ResidueField/Separable.lean: the class itself requires
prime p; perfect base residue plus integral extension supplies the class.
The current source introduces span(q).IsPrime BEFORE requesting this class.
RingTheory/DedekindDomain/Dvr.lean: actual nonzero prime localization of a
Dedekind domain is a DVR; nonzero follows from the original nonzero q image.
RingTheory/Ideal/GoingUp.lean: nonempty_primesOver requires actual integral
and faithful extension. The canonical normal closure satisfies both.
RingTheory/Ideal/Over.lean: over_def is p=P.under A, so its SYMMETRY produces
the center equality used here. No unspecified prime or reverse map is used.


## Exact geometric points and original Spec maps

Read pinned FieldTheory/IsAlgClosed/AlgebraicClosure.lean: literal
AlgebraicClosure k has the original algebraMap from k, a Field instance and
IsAlgClosed instance. A field ring hom is injective; this proves the actual
geometricPoint kernel rather than assuming a residue embedding kernel.

Read accepted SourceBranchResidueInertia318.kernel_inertia_iff and
SourceBranchPointAction318.fixed_iff in full. The generic versions here use
the same primary Ideal.mem_inertia (all x: sigma*x-x in P), actual RingHom
kernel, and contravariant Spec.map_comp/Spec.map_injective. The new source
retains SAME original galRestrict map and original P, not those source-specific
Contact maps as substitute geometric input. Accepted InfinitySignPoint318
was also read for the exact CommRingCat.Hom.hom/Spec.map_injective direction.

Pinned Ideal.algebraMap_residueField_eq_zero identifies the original prime.
Original coordinate equalities are mapped Polynomial.X-C(contact_k), not
unverified numerical identifications. Prime/irreducible associated_of_dvd
plus irreducible_X_sub_C identifies exactly the original linear prime.
The whole-curve cancellation is categorical cancel_mono j, with actual
schemeMap(sigma)>>j=j>>a(sigma) explicitly required for every original sigma.
The morphisms are contravariantly induced affine automorphisms; no unproved
covariant group-action convention or arbitrary action conjugacy is asserted.


## Exact finite residue and complex embedding primary APIs

Pinned mathlib commit56a005855ea17e0b0958f73ec801ae140b0a1679 read directly:

* RingTheory/Ideal/GoingUp.lean, Ideal.IsMaximal.of_liesOver_isMaximal:
  integral A->B, P.LiesOver p, p maximal and P prime imply SAME P maximal.
  Original center equality is reversed only to construct P.LiesOver span(q).
* RingTheory/FiniteType.lean, Module.Finite.finiteType and
  Algebra.FiniteType.trans: actual tower with both finite-type premises.
  The Q algebra maps are explicitly the original composed maps, with literal
  IsScalarTower.of_algebraMap_eq witnesses. Q[t] and the original Order are
  not replaced by unrelated finite-type algebras.
* RingTheory/LocalRing/ResidueField/Ideal.lean, instance for maximal I:
  Module.Finite R I.ResidueField, constructed from original surjective
  algebraMap. Its original kernel is Ideal.algebraMap_residueField_eq_zero.
* RingTheory/Jacobson/Ring.lean, finite_of_finite_type_of_isJacobsonRing:
  CommRing R, Field S, Algebra R S, Jacobson R, FiniteType R S imply
  Module.Finite R S. Applied to Q and SAME P.ResidueField, not its fraction
  field chosen anew. Q is a field and hence Jacobson.
* FieldTheory/IsAlgClosed/Basic.lean, IsAlgClosed.lift: an algebraic original
  extension embeds into an algebraically closed extension. The actual finite
  Q-residue extension supplies algebraicity; field injectivity proves exact
  original kernel after composition.
* Analysis/Complex/Polynomial/Basic.lean, Complex.isAlgClosed supplies C's
  actual algebraic closedness by the fundamental theorem of algebra.

Exact primary copies used by the author are retained in
build/cohomology-primary/complex-points/ (and prior full-inertia/IdealGoingUp.lean).
The unchanged original Spec-valued point/action/cancel_mono and contact prime
comparisons are in the prior44 exact copies. No analytic-to-algebraic theorem
is asserted or imported as an assumed consequence of this embedding step.
Mathlib_Analysis_Complex_Polynomial_Basic.lean: 13d260a9e2a69b8a90d5807e75806f296d7ab026c14e2a8f08708b8a28554a08
Mathlib_FieldTheory_IsAlgClosed_Basic.lean: 69b6cb4982cefd55663fa1660aa8068b2ce9a05f74b5d1c6e77292337fe3bc29
Mathlib_RingTheory_FiniteType.lean: 7c17261adb1bc3c026a242e5ffcb88e17aa738019502c5358abdacb7e5c67250
Mathlib_RingTheory_Jacobson_Ring.lean: 2bb61c268a86353b5f8ec16eb6c2108bbfc366061a3d534ea89ddd365fe65826
Mathlib_RingTheory_LocalRing_ResidueField_Ideal.lean: 1108bc3794a0bae394e967ebc318634cfc25eed50d4bc0c53ba50293cb9867b0
