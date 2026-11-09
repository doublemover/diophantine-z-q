# Actual positive normalizer norm-parity quotient

Construct the actual positive-reduced-norm normalizer of the original quaternion order and its16-element reduced-norm-parity quotient, retaining the original prime words and actual five fixed-point inertia representatives.

This is expressly the quotient by the kernel of the actual norm-parity map. It does not assert that this kernel equals rational scalars times original integral units, or identify the resulting finite quotient with a canonical deck group.

## Application obligations

1. **Same original rational and integral objects.** Required: A formal finite group must not substitute for the actual quaternion normalizer. Constructed: All46 predecessors are exact. The ambient group is units of the same original rational quaternion algebra; the actual normalizer is defined by both integral conjugation directions on every element of the same original order. Evidence: verification/SOURCE-COPIES.json; PELActualOrderNormalizer318.normalizer.

2. **Genuine reduced-norm character.** Required: The quotient map must be defined on actual elements and be multiplicative, including rational denominators. Constructed: Proves actual reducedNorm multiplication; parity is the integer rational valuation at the original primes2,3,5,7 reduced mod2, including negative valuations. The original division proof supplies nonzero norms before applying padicValRat.mul. Evidence: PELQuaternionNormParity318.norm_mul; parity; parity_mul; parityHom.

3. **Scalar and unit convention.** Required: Do not silently drop rational scalars or replace the specified arithmetic units. Constructed: Actual rational scalars have reduced normq², hence zero parity. Original norm-one integral units also have zero parity. Equality of the parity kernel with scalar times integral units is not asserted. Evidence: PELQuaternionNormParity318.scalarUnit; parity_scalar; integralUnit; parity_norm_one.

4. **Actual normalizer subgroup and coverage.** Required: Prime representatives must lie in the actual two-sided normalizer, not just have suitable norms. Constructed: Both-direction whole-order normalization proves prime_mem. Group closure and inverse are proved using the original integral property. All ordered original prime words are then members. Original integral units normalize the same order, yielding membership of all five actual inertia normalizers via their exact connecting units. Evidence: PELActualOrderNormalizer318.normalizer; prime_mem; word_mem; integral_mem; inertia_mem.

5. **Positive real orientation.** Required: The real PEL component uses positive norm, not the accidentally larger orientation-reversing group. Constructed: positiveNormalizer is the actual normalizer restricted to positive reduced norm, with multiplication and inverse closure proved from the actual norm. All prime words and the original five representatives belong by their explicit positive norms. Evidence: PELPositiveOrderNormalizer318.positiveNormalizer; prime_mem; word_mem; inertia_mem.

6. **Surjectivity before counting.** Required: A claimed16-element quotient must have actual representatives for every binary vector. Constructed: Each actual prime normalizer has its corresponding single basis bit. The ordered original word realizes every v in Fin4→ZMod2. This supplies an explicit right inverse on the actual positive normalizer, not merely a cardinality argument. Evidence: PELQuaternionNormParity318.parity_prime; parity_word; PELPositiveOrderNormalizer318.parity_word; parity_surjective.

7. **Exact quotient and original inertia transport.** Required: The quotient kernel and directions must remain explicit. Constructed: QuotientNormalizer is positiveNormalizer divided by the kernel of its actual parity hom. The pinned first-isomorphism theorem with explicit right inverse gives the actual group equivalence, cardinal16 and all representative classes. Both actual inertia representatives and their original-label prime words have the same class; all five classes are distinct. Evidence: PELNormalizerParityQuotient318.quotientEquiv; quotientEquiv_mk; quotient_card; every_class; inertia_class; inertia_classes_injective.

8. **Historical and canonical scope.** Required: Norm-parity quotient is not automatically the full canonical normalizer/deck quotient. Constructed: This constructively supplies a finite quotient of the actual positive normalizer. It does NOT prove parity kernel=Q×O×, full normalizer class exhaustion for that smaller kernel, canonical geometric/Galois action, branch-position matching, algebraic abelian scheme, or contact-Jacobian/PEL-surface identity. These joins remain explicit. Evidence: README.md; verification/historical-source-pins.json.

9. **Validation and primary APIs.** Required: Primary theorem assumptions and exact object identity must be checked independently. Constructed: Pinned PadicVal.Basic requires prime Facts and nonzero rational inputs for multiplication, all supplied; negative integer valuations retained. Pinned QuotientGroup.Basic applies to the actual group hom with its constructed right inverse. Independent exact checker covers norm multiplication, all16 actual words and parity, original five labels, rational scalar parity and integer-coordinate normalization. No local Lean. Evidence: verification/check_parity.py; verification/PARITY-PRIMARY-SOURCES.json.

## Validation and open join

No local Lean compilation. Hosted strict-module recursive audit and independent acceptance pending. Norm-parity kernel identification, original geometric branch images/cross-ratios and algebraic PEL moduli realization remain separate.
