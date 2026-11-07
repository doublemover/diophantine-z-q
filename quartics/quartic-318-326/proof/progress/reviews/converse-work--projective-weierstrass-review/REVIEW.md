# Independent review: actual projective Weierstrass cubic

Accepted at the declared scope. All seven producer modules were copied without edits, strictly rebuilt with kernel type checking enabled, and recursively audited: 217 declarations, only propext, Classical.choice, and Quot.sound. The copied source hashes were checked against the frozen originals after replay.

## Mathematical interface checks

1. The ambient object is Mathlib's genuine Proj of the graded polynomial ring in three variables. Its proper base map is transported through the proved degree-zero constant-ring equivalence to the original arbitrary commutative base R. The actual chart maps commute with this same base map.
2. Generic dehomogenization and its inverse are algebra homomorphisms on the actual degree-zero homogeneous localization. The inverse proof uses the actual homogeneous scaling identity and injectivity into the full localization, not a field-valued point argument. Standard chart ranges and their covering are proved.
3. The finite and infinity maps to projective space use [x:y:1] and [u:1:z]. Their compatibility is proved on the actual localized coordinate ring through homogeneous evaluation and actual Proj overlap maps. Thus the pushout morphism is the existing two-chart cubic map, not a replacement object.
4. CubicChartGeometry318 proves exact inverse-image open sets D(Z) and D(Y) using the genuine overlap open immersions and pushout condition. Its finite_pullback and infinity_pullback are actual categorical pullback squares. Their use to obtain closed restrictions is scheme-theoretic, not just pointwise image membership.
5. For a homogeneous prime containing Y²Z−X³−AXZ²−BZ³, simultaneous Y,Z membership forces X³, then X membership. This contradicts the actual standard-open cover. Consequently there is no missing point confined to the X chart, over arbitrary base rings and residue characteristics.
6. The homogeneous cubic's exact support equals the actual image. The forward inclusion follows by evaluating the literal polynomial in both quotient rings. The reverse inclusion uses the just-proved chart cover, exact dehomogenizations, and the prime-spectrum image theorem for the genuine quotient maps.
7. Closedness is not inferred from closed image alone. The map first has a separately proved preimmersion structure, obtained from the two actual closed chart restrictions on an open neighborhood of its image. Mathlib's preimmersion means topological embedding plus surjective stalk maps. Closed image then gives a closed immersion by the corresponding theorem. This inference and its exact imported definition were checked.
8. Properness is composition of this actual closed immersion with the actual proper projective-plane base map. embedding_over_base identifies that composite with the original two-chart structure morphism. Separatedness follows; the actual infinity section is a closed immersion by separatedness/properness and its section identity.

## Exact remaining scope

No discriminant invertibility is required for properness; arbitrary A,B and base rings are legitimate. The packet does not assert an additional homogeneous-quotient Proj identification. It does not establish the full group law, elliptic/abelian scheme package, primitive torsion splitting, or the remaining modular/PEL/global realization. Those remain separate tasks. No mismatch was found, and the original frozen packet was not changed.
