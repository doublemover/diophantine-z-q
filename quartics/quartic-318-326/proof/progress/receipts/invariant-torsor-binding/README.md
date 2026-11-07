# Bind the actual invariant-base torsor

This packet removes the remaining change-of-base gap between the original equivariant splitting and the regular splitting over the actual invariant algebra. It does not identify those two base rings.

Given an R-algebra B, a finite group G acting through the actual supplied algebra automorphisms rho_g, a free action on X, a faithfully flat R-algebra S, and an actual equivariant splitting

    S tensor_R B = (X -> S),

`InvariantRegularSplit318.invariantTorsorEquiv` constructs the canonical algebra isomorphism

    B tensor_{B^G} B = (G -> B).

`invariantTorsorEquiv_tmul` proves its exact formula b tensor c -> (g -> b*rho_g(c)). Neither a regular splitting over B^G nor a torsor-map isomorphism is an input.

## Actual constructions

`TensorTower318` constructs the scalar-extended algebra inclusion and the actual pushout for every tower R -> A -> B. It supplies

    (A tensor_R S) tensor_A B = B tensor_R S,

with exact pure-tensor formula. All algebra structures and scalar-tower compatibilities are checked.

For A = B^G, `InvariantRegularSplit318` then:

1. Uses the preceding actual invariant-base-change equivalence to identify A tensor_R S with the actual fixed-function algebra on X.
2. Checks that this identification and the original cover identification preserve the actual intermediate inclusion.
3. Uses the free-orbit algebra trivialization to construct a regular splitting over A tensor_R S.
4. Applies the actual tensor pushout to obtain the regular splitting of (A tensor_R S) tensor_A B.
5. Checks its exact group action, including the pullback convention g*h, on generating pure tensors.
6. Uses faithful flatness of the actual extension A -> A tensor_R S and the proved canonical-map descent theorem to construct the original torsor algebra isomorphism over A.

No group-order inversion, normality, domain assumption, supplied quotient algebra, supplied canonical map isomorphism, or assumed invariant-base trivialization is used.

## Remaining geometric input

The actual primitive elliptic torsion scheme, its faithfully flat equivariant splitting, and the identification of its free diamond action with the supplied finite set action still need geometric realization. The full source modular/sheaf quotient and normalization identification remain external. The new result closes the actual invariant-base transport and canonical torsor identity, not those other geometric objects. RefinedGeometricRealization and FiveContact49Height remain unasserted unconditionally.

Run `bash build.sh` for a fresh strict-kernel rebuild of both modules and exhaustive recursive axiom audit. Imported Mathlib and frozen project dependencies use the pinned shared cache. No repository or Git edits were made.
