# Level-three projective j chart certificates over Q

Status: uncompiled inactive candidate. Hosted Lean checking and distinct
non-author review are pending. No local Lean build or accepted proof is claimed.

This packet provides the smallest concrete algebraic inputs to gluing the actual
projective j morphism: exact degree-four homogeneous coordinates, explicit
Bezout certificates covering both entire rational affine source charts, exact
overlap scaling, and consumers identifying both chart expressions with the
original modular j function at every original quotient point.

The characteristic-three obstruction is a theorem statement, not merely a
warning in prose. The same homogeneous pair has a base point at [0:1] in
characteristic 3. All claimed prime-spectrum coverage here is over Q.

## Exact application contract

1. Exact homogeneous pair and degree. Required: The original j formula on T must determine the pair, rather than a merely isomorphic rational function. Constructed: homogeneousNumerator(x,y)=(x+27y)(x+243y)^3 and homogeneousDenominator(x,y)=x^3y; numerator_scale and denominator_scale prove common degree four. Application: Both scale by exactly a^4. No degree-preserving Proj.map application is made, since the pinned API cannot directly accept this degree-four substitution.

2. Full finite source chart over Q. Required: The numerator and denominator must generate the unit ideal on all of Spec Q[T], not only on complex closed points. Constructed: finite_bezout proves A*F-B*G=3^27 with A=38T^2-972T+19683 and B=38T^3+27756T^2+6764391T+550572876. Application: finite_coprime divides this exact identity by the nonzero rational 3^27. Thus coefficient inversion is explicit; no Z-coprimality is inferred.

3. Full reciprocal source chart. Required: Coverage must include the reciprocal origin corresponding to source infinity. Constructed: reciprocalNumerator=(1+27S)(1+243S)^3, reciprocalDenominator=S; reciprocal_bezout proves F-BG=1. Application: The reciprocal coefficient B is 756+196830S+19131876S^2+387420489S^3. The identity is checked by ring normalization and directly gives reciprocal_coprime.

4. Prime-spectrum open coverage. Required: Every prime in both affine source charts must lie in a target-coordinate domain. Constructed: finite_basicOpen_cover and reciprocal_basicOpen_cover prove D(F) sup D(G)=top in their actual prime spectra. Application: The generic helper applies the exact Bezout equality inside an arbitrary prime ideal. Simultaneous membership of F and G would put 1 in that proper ideal. It does not restrict to maximal ideals, geometric points or a dense open.

5. Overlap and scalar compatibility. Required: Finite and reciprocal source expressions must represent the same homogeneous pair with an explicit invertible scalar on the overlap. Constructed: chart_pair_overlap proves N(T,1)=T^4 N(1,S) and D(T,1)=T^4 D(1,S) under TS=1 over every commutative ring. Application: The two identities specialize the degree-four scaling lemmas. The common T^4 is retained. This provides the ring-level comparison input for later scheme-chart gluing, not the gluing itself.

6. Geometric nonvanishing and characteristic restriction. Required: No common projective zero in characteristic zero, without silently extending that claim to all integral fibers. Constructed: no_common_zero handles every nonzero homogeneous pair over a characteristic-zero field; characteristic_three_base_point exhibits the nonzero pair [0:1] where both coordinates vanish in ZMod 3. Application: The proof splits x^3*y=0 and uses 27 and 243 nonzero only with CharZero. The explicit characteristic-three counterexample prevents treating the same pair as an everywhere-defined Z-model.

7. Identity with actual polynomial evaluations. Required: The polynomials reserved for the scheme charts must evaluate to the original complex rational j function. Constructed: finite_evaluation and reciprocal_evaluation identify both coordinates; finite_J and reciprocal_J identify their quotients with ThreeCompactParameter318.J. Application: The reciprocal formula explicitly requires T nonzero before denominator cancellation. Finite formula includes every T as a field expression; actual quotient inputs separately carry the required nonvanishing.

8. Original modular consumer and boundary values. Required: The exact original quotient j map must be consumed at all original points, and both boundary source origins must have specified chart values. Constructed: original_j_finite and original_j_reciprocal consume quotientParameter_j; original_finite_denominator_ne_zero consumes quotientParameter_ne_zero. boundary_chart_values gives (3^18,0) at T=0 and (1,0) at S=0. Application: The original quotient theorem includes elliptic points. No generic-locus identity is substituted. Both boundary coordinate pairs select the target reciprocal chart, but no pole order, morphism or arithmetic descent follows solely from these scalar values.

9. Verification and bounded next step. Required: The changed application needs hosted kernel checking and distinct review before acceptance. Constructed: Four predecessor sources are byte-identical to the frozen atlas-r2 closure; two new modules and all imports are hashed in intake.json. Application: This is an uncompiled inactive candidate. It supplies exact basepoint-free charts over Q and modular scalar comparison, not a global projective j scheme morphism. Next work must construct localization-based scheme maps, prove all overlaps and glue them; no first-batch packet is modified.

## Remaining work

Construct the actual scheme maps on D(F) and D(G), prove their agreement using
the exact homogeneous-evaluation maps, and glue over each source chart and then
the full projective source. Bind the resulting scheme-valued map to the compact
analytic comparison, including the two cusps. None of this gluing is inferred
from coprimality alone. No degree-preserving Proj.map shortcut or everywhere
integral Z-model is used. PEL and universal-family realization remain separate.
