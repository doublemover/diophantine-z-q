# Exact quartic algebra, Laurent degree and global scheme finiteness

Status: uncompiled inactive hosted-CI candidate. Non-author source review and
hosted Lean checking remain pending. No local Lean build was run.

This larger bridge constructs the universal monic quartic over the original
j-line and identifies it, in both directions, with the original Laurent source
ring. The root is explicitly a unit, the coefficient j is exactly N(T)/T^3,
and the retained j scalar action makes the Laurent algebra finite free of rank4.
Its compatible fraction fields have degree4 with the same scalar generator.

The induced finite affine Spec map satisfies an exact scheme-level square with
the existing global projective j morphism. The Laurent open has a finite
complement in the actual scheme prime space, proved using both original affine
charts. Therefore every actual scheme fiber of the global map is finite.
Properness of the original projective source and the exact over-Q identity
supply properness of that map; proper plus quasi-finite proves global IsFinite.
This argument does not infer scheme finiteness from complex-point fibers.

The generic degree statement in this packet is for the explicitly compatible
fraction fields of the identified j/Laurent algebra. Identifying those fields
with the actual projective generic stalks and their actual pullback remains a
separate step. Global flat rank, a complete branch divisor, PEL/universal-family
realization and the full318/326 theorem are not claimed.

## Exact application contract

1. Exact universal quartic over the j-line. Required: The degree algebra must use the original j coordinate, exact numerator scale and original Laurent source parameter. Constructed: ThreeJMonicAlgebra318 defines Base=Q[j] and the monic outer quartic T^4+(756-j)T^3+196830T^2+19131876T+387420489, then Model=AdjoinRoot of this polynomial. Application: Its root relation is explicitly rearranged to (T+27)(T+243)^3=jT^3. Monicity gives a genuine power basis and finite-free module of rank4, without assuming irreducibility.

2. Constructed inverse of source parameter. Required: Identifying the algebra with the original punctured source requires actual invertibility of its root. Constructed: inverseT is an explicit cubic polynomial in T and j, scaled by -1/387420489 in Q. t_inverseT proves their product is1 from the monic relation. Application: The rational scalar multiplication identity is checked through algebraMap Q Model. j_expression then cancels T^3 only using the constructed inverse, retaining every original coefficient. This is a Q argument and does not extend through characteristic3.

3. Actual Laurent equivalence in both directions. Required: An abstract rank4 algebra is insufficient; both inverse ring maps to the exact original Laurent source must be constructed. Constructed: forward is AdjoinRoot.liftAlgHom sending root to original T and coefficient j to N(T)S^3; backward is the actual localization lift sending original T to the root. Application: The Laurent TS=1 identity proves the defining relation. backward_s equals inverseT by uniqueness of inverses; backward_jLaurent equals j by the exact numerator relation. Localization and AdjoinRoot extensionality prove both compositions are identities, including the base coefficient map.

4. Exact scalar action, rank and fraction-field degree. Required: Ranks must be computed for the j pullback, not the pre-existing T-coordinate algebra structure on the same Laurent ring. Constructed: jAlgebra is explicitly baseMap.toRingHom.toAlgebra. baseCoordinateEquiv is promoted over this exact Q[j] action and transfers finite freeness and rank4. Application: Model is a domain through its Laurent equivalence. Compatible fraction fields use the canonical lifted coefficient map; fraction_degree_four applies the simultaneous fraction-ring finrank theorem, and fraction_scalar_j identifies the image of the original j generator. This does not yet identify the actual projective generic stalks.

5. Scheme-level consumer of the finite algebra. Required: The finite algebra morphism must be tied to the existing global projective scheme map, not merely to a scalar expression. Constructed: finiteTargetMap is literal Spec.map of the same baseMap. finiteTargetMap_finite follows from the exact finite module structure. original_scheme_square identifies embedding followed by global map with finiteTargetMap followed by original target chart1. Application: The square consumes the exact global finite_restriction and denominator evaluation formula on the whole original Laurent ring. The inverse of T^3 is the original S^3; numerator evaluation is explicitly identified with jLaurent. No dense-point inference replaces this equality of scheme morphisms.

6. All source scheme points outside Laurent open. Required: Global scheme finiteness needs coverage at every prime, not merely complex points or generic points. Constructed: ProjectiveLineLaurentComplement318 proves affine primes containing X form a subsingleton using maximality of the principal ideal(X). The full projective complement is contained in the union of their images under both original charts. Application: chart_mem_laurent uses the exact original full_intersection and both chart preimage identities. The original Fin2 projective open cover supplies every source point. Thus the complement of the unchanged original Laurent embedding is finite as a set of scheme points.

7. Full scheme fibers and actual properness. Required: Finite complex-point fibers cannot imply scheme quasi-finiteness without an additional argument. Constructed: finite_scheme_fiber uses the finite Laurent Spec map, injectivity of the original finite target chart, the exact scheme square and the proved finite source complement. map_proper uses over_Q and the actual proper projective structure morphism. Application: Every global fiber is contained in the image of the finite restricted fiber union the finite source complement. This covers generic and nonclosed points as well as closed points. Properness is of the exact constructed global map via the separated original target structure.

8. Global scheme-theoretic finiteness. Required: The proper/quasi-finite theorem must receive its complete hypotheses on the same morphism. Constructed: map_locallyQuasiFinite applies the finite-scheme-fiber criterion to the locally finite type map supplied by actual properness. map_finite applies IsFinite.of_isProper_of_locallyQuasiFinite. Application: Both instances refer to ThreeProjectiveJMap318.map, and every fiber is covered by the preceding argument. This proves scheme finiteness in the draft, without presuming the finite target open is the entire preimage or omitting the second target chart.

9. Verification, historical scope and remaining identification. Required: New degree and finiteness applications require exact primary references, hosted Lean and distinct review before proof acceptance. Constructed: Five new modules extend60 unchanged sources and one narrowly repaired predecessor. The source draft now includes actual global scheme finiteness, an exact finite-free Laurent presentation and degree4 of its compatible fraction fields. Application: Structural/hash checks are not kernel validation. The actual projective generic-stalk pullback still needs identification with these explicit fraction fields before stating its finrank4; global flat rank and complete branch divisor remain separate. The same original analytic holomorphy and cusp/elliptic point comparisons are inherited unchanged. PEL/universal-family realization and full318/326 arithmetic completion are not asserted.

