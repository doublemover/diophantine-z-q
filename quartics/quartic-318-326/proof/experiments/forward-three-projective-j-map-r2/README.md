# Global projective level-three j morphism over Q

Status: uncompiled inactive hosted-CI candidate. Distinct non-author source
review and strict Lean checking are pending. No local Lean build was run.

This packet completes the source-level gluing construction on the original
ProjectiveJLine318.scheme Q. It first proves an exact denominator-localization
evaluation formula for the previously glued whole affine map. On the original
Laurent overlap both denominators are units, so both maps use the same finite
target chart; the exact fourth-power coordinate identity proves equality of
scheme morphisms there. The original projective cover then glues the two maps.

The construction does not use a degree-four substitution in the degree-preserving
Proj.map API, a generic-point extension, a point-count argument, or a different
projective source. The global map has exact restrictions to both original affine
maps and preserves the original rational structure map.

## Exact application contract

1. Original rational coefficient and source objects. Required: The global source and target must be the existing ProjectiveJLine318.scheme Q with their actual original affine charts. Constructed: The new map has type ProjectiveJLine318.scheme Q to itself and uses JLineAtlas318.cover Q. Both affine maps are the exact prior ThreeAffineJMaps318 finiteMap and reciprocalMap. Application: No newly glued replacement scheme is substituted for the original Proj. All polynomial rings, affine chart maps and structural maps retain the same rational coefficients.

2. Exact denominator localization factorization. Required: When a polynomial denominator becomes a unit in an arbitrary Q-algebra, the source scheme morphism must factor through its actual localization. Constructed: evaluation_formula constructs liftG by IsLocalization.Away.liftAlgHom from a specified inverse v of the actual image of g. Application: hbase identifies the ring map on every original polynomial, and hfac proves the contravariant Spec factorization by ring-hom extensionality. This is not a pointwise or fraction-field argument.

3. Inverse coordinate and original local-map identity. Required: The factorization must evaluate the exact original denominator chart, with the right inverse and coefficient map. Constructed: The image of invSelf g is proved equal to v by the two multiplication-to-one identities. Polynomial.ringHom_ext then checks the composed evaluation on constants and X. Application: The prior denominator_restriction theorem is applied to the same glued affine map. The resulting map is literally Spec of evaluation at phi(f)*v followed by original target chart 1. No alternative projective parameter or unconstrained coefficient map is introduced.

4. Entire original source overlap. Required: The overlap must be the actual original projective-chart intersection, not a dense generic subset. Constructed: ProjectiveLineOverlap318.A is the original localization Q[T,T^-1], with finiteInclusion and infinityInclusion and the proved actual_pullback. Application: The exact original elements t and s satisfy ts=1. finite_denominator_inverse proves t^3 has inverse s^3, and reciprocal_denominator_inverse proves s has inverse t. Therefore the entire overlap, including zeroes of the numerator, factors through the finite target chart.

5. Explicit fourth-power scaling and cancellation. Required: The two affine coordinate expressions must agree using the exact homogeneous scaling, with every canceled factor justified. Constructed: overlap_coordinate specializes chart_pair_overlap to t,s and retains its t^4 factor before multiplying by s^3. Application: The identity t^4*s^3=t follows solely from ts=1 in the actual Laurent ring, not from a domain or nonzero-field cancellation. The finite and reciprocal rational polynomial evaluations are then equal as elements of that ring.

6. Equality of actual overlap scheme maps. Required: The two whole affine scheme maps must agree after precomposition by the original overlap inclusions. Constructed: affine_overlap applies evaluation_formula to aeval t with inverse s^3 and aeval s with inverse t, and rewrites the exact coordinate identity. Application: evaluation_t identifies aeval t with the original localization algebra map, checking constants and X. Both composites become the same actual polynomial evaluation morphism followed by the same target chart, proving equality of scheme maps on the entire categorical intersection.

7. Complete projective gluing compatibility. Required: Every ordered pair of the two original projective chart indices must satisfy the canonical pullback compatibility required by glueMorphisms. Constructed: localMap sends chart 0 to reciprocalMap and chart 1 to finiteMap. compatible treats all four ordered Fin 2 pairs. Application: Mixed pairs consume the original actual_pullback and its flip, with affine_overlap in the matching direction. Diagonal pairs use chart monomorphism cancellation. The complete original JLineAtlas318.cover supplies source coverage; no chart or special point is omitted.

8. Exact global consumer and coefficient map. Required: The resulting global morphism must restrict to the exact intended local maps and preserve the same Q structure morphism. Constructed: map is cover.glueMorphisms on the original source. finite_restriction and reciprocal_restriction are the exact original chart composites. over_Q proves the same rational coefficient map. Application: The original cover hom_ext checks over_Q on both original affine charts. The prior affine over_Q identities and original chart_over_base theorem match those exact restrictions. These identities bind the construction to the actual Proj, not merely a map with matching values on a generic locus.

9. Verification and excluded downstream conclusions. Required: Every new application needs hosted kernel checking and distinct review; the arithmetic boundary must remain explicit. Constructed: Nine unchanged local-map-stage sources and two new localization-consumer/projective-gluing modules are hashed in an eleven-source inactive candidate. Application: No local Lean execution or pass receipt is claimed. This source draft constructs the global Q scheme morphism, but the exact compact analytic/scheme-valued j comparison, degree and ramification theorems, integral extension through characteristic 3, universal-family and PEL realization remain separate. The characteristic-three counterexample is retained unchanged.

## Remaining realization and verification

After hosted checking, bind the map on actual complex-valued points to the exact
compact level-three analytic comparison, including both cusp origins. Prove
any required degree, ramification or finite-map statements for this exact
morphism separately. The characteristic-three base point prevents treating the
same coordinate pair as an everywhere-defined Z-model. Universal-family and
quaternionic PEL identifications, arithmetic descent and the full 318/326 theorem
are not consequences of this gluing alone and remain separate.

The nine predecessor modules are unchanged from forward-three-j-local-maps-r1.
No submitted or failed-stage source packet was edited. This candidate may replace
its smaller predecessor in a future CI matrix to avoid duplicate compilation.

## Hosted-failure revision

Propagate the two exact hosted certificate repairs into the full eleven-module projective-map closure. The rational polynomial identity now explicitly rewrites map_pow and map_ofNat for C instead of relying on the simp set. The characteristic-three base point now proves the small closed equality 27=0 in ZMod 3 by kernel decide before simplification, rather than asking norm_num to reduce a large residue. All other ten source modules are unchanged. The global gluing modules were not reached by that earlier six-source CI run and remain uncompiled.

The failed source stage remains unchanged. Exact run 42573367792 at commit
272c0fc evidence is retained under previous-failure. No local Lean was run;
this repair is pending hosted checking and distinct review.
