# Literal infinity coordinate-ring sign involution: current source contract

Own zero-r44 and cotangent-r50 artifacts, run43603177874 at57227e167abe49436d651b932ff75d5bdf9b5898. Before/after/native/actual-consumer hashes are in SIGNS-MANIFEST.json. No local Lean or candidate pass.

## 1. Required native input
Pinned map_mul in Mathlib/Algebra/Group/Hom/Defs.lean326 requires a MulHomClass map and arbitrary multiplicative inputs, and states f(x*y)=f(x)*f(y). The map is the existing algebraMap ℂ (FourRootInfinityCoordinateRing318.Ring b). The current residual is exactly a product of its two scalar images squared. Reverse map_mul restores its literal image-of-product presentation before applying existing double_scalar_square.

## 2. Actual construction
The original finiteEnd, infinityEnd, finiteEquiv and infinityEquiv are untouched. They act on the exact polynomial-quotient rings with their original relations, not on only their complex point sets. b remains any Fin4→ℂ and g the full FourBinaryCharacters group. Both maps still square to identity on the same algebra.

## 3. Full coverage
The existing hom_ext proof still covers the none generator and every some i, i:Fin4. The none branch remains unchanged, and the some branch receives the single reverse map_mul rewrite. All16 sign tuples, all b including repeated roots and every ring element remain quantified. No generic or distinct-root condition is added.

## 4. Maps and directions
AlgHom.comp_apply, infinity_ratio and AlgHom.commutes reduce the composite endomorphism at a ratio generator. Existing left reassociation and reverse pow_two produce (map(c_i)*map(c_0))² times the generator. Reverse map_mul makes (map(c_i*c_0))²; double_scalar_square then yields1. Composition direction and the original map remain literal, not replaced by a point-bijection transport or new algebra structure.

## 5. Scalars and normalization
Each c_i is the original sign character, c_i²=1. Both sign factors and their order are retained, including the distinguished root0 ratio normalization at infinity. No omitted sign, scaling or field-extension argument occurs. The existing double_scalar_square proof is unchanged and itself uses native map_pow and both character-square identities.

## 6. Actual downstream consumer
FourRootActualResidueInertia318.infinity_inertia uses this exact infinityEquiv and its infinity_point compatibility to identify inertia at the kernel of the actual infinityEvaluation. Its finite_sign_inertia similarly consumes finiteEquiv/finiteEnd/finite_point, unchanged. FourRootActualOrderAutomorphisms318.polynomialSign identifies the original polynomial sign with finiteEquiv; FourRootActualGenericSigns318 compares finiteEnd on the literal generic field. Exact consumer sources are preserved; no later ideal-inertia or generic-field acceptance is inferred.

## 7. Exceptional cases
All normalized infinity generators and finite generators are retained. The proof does not exclude zero coordinates or branch points, impose root separation, rationalize the coordinate ring or shrink the deck group. Characteristic and scalars remain ℂ. Public statement text, assumptions and resource options are unchanged.

## 8. Observed history
Both own current logs show rewrite double_scalar_square cannot match because its pattern is (algebraMap(...product...))² whereas the goal contains (algebraMap(c_i)*algebraMap(c_0))². Their preceding NormalizedSignAction module genuinely passed. This edit addresses only the exact representation mismatch; no additional claim about untouched later errors is made.

## 9. Verification boundary
One proof-body rewrite is added. No new definition, theorem telescope, assumption, placeholder or limit change. The candidate requires independent current source/contract and complete-copy propagation review and actual hosted Lean. A source-supported same-map proof is not kernel or full packet acceptance.
