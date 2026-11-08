# Actual primitive-three splitting and pointed model

This packet continues the frozen `relative-three-torsion` algebra. Let R be a nontrivial commutative ring, let 3 be invertible, and suppose the short-Weierstrass discriminant −16(4A³+27B²) is a unit.

The constructed rank-eight algebra is the quartic third-division x algebra followed by the actual quadratic relation y²=x³+Ax+B. This packet constructs its coordinate negation, a finite étale faithfully flat extension T, and an actual T-algebra equivalence

T ⊗_R B ≃ (Fin 4 × Bool → T).

The extension first splits the separable x quartic, then adjoins a square root of the invertible cubic value at each of its four roots. Evaluation at both y signs gives the displayed isomorphism. Surjectivity is proved by interpolation using the inverses of 2 and the four y roots; equal finite free ranks then give injectivity. These are actual algebra maps, not a point-count comparison.

A concrete bijection labels these eight evaluations by the actual primitive pairs modulo three. The full unit group (Z/3Z)× is {1,−1}, and coordinate negation exchanges each opposite pair. The resulting splitting is diamond-equivariant, with the action composition identity proved. This is a scalar-equivariant labeling only: no assertion says this arbitrary choice of four opposite pairs is an additive level-three basis or a symplectic/full-level-three structure.

For every diamond subgroup H, the canonical tensor map B ⊗_(B^H) B → (H → B), sending b ⊗ c to the function g ↦ b·g(c), is proved to be an algebra isomorphism. This is an actual torsor map, with no supplied splitting or freeness premise.

The actual map from the affine elliptic-family coordinate algebra onto B is proved surjective, hence the rank-eight equation family is a closed subscheme of the affine curve. The literal integral open-j base at level three supplies the concrete algebra, splitting, and action to the existing pointed-component construction. The field-valued point β is still an explicit input; its actual H-quotient component has a proper flat surjective normal arithmetic model.

## Remaining boundaries

The field-point identification with exact order three was proved in the predecessor packet. Identifying this relative equation subscheme with the complement of the identity in the kernel of an actual global multiplication-by-three Scheme morphism remains open. This packet does not construct the full global group law, general-N primitive torsion, the manuscript's PEL/Shimura source, a universal abelian surface, or its full-level-three marking. It does not prove the final Diophantine theorem.

## Verification

`build.sh` rebuilds all eight modules with `debug.skipKernelTC=false` and then audits every declaration from them recursively, accepting only `propext`, `Classical.choice`, and `Quot.sound`. Run it under the shared exclusive compiler lock. The final receipt identifies the exact replay and source hashes. This is an author replay, not an independent review or manuscript incorporation.
