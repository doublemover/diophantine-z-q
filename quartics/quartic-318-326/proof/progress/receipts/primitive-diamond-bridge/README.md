# Actual primitive diamond action and torsor binding

This packet uses the existing `PrimitiveTorsion318.Primitive` predicate, with no replacement notion of primitive point. For every nonzero natural N it proves:

1. `gcd(N,gcd(x.val,y.val))=1` if and only if an actual pair of residues a,b satisfies ax+by=1.
2. Multiplication of both coordinates by a unit preserves that predicate. The resulting actual unit action, and every diamond subgroup action, are free.
3. This coordinate action is actual multiplication on the actual complex elliptic curve through `EllipticTorsion318.torsionMap`. Every actual point of exact order N has free scalar-unit action.
4. `primitiveTorsorEquiv` specializes the previously proved faithfully flat invariant-base torsor construction to these actual primitive pairs. Its map on pure tensors is exactly b⊗c ↦ (g ↦ b·ρ_g(c)). No freeness premise or supplied canonical torsor-map isomorphism remains.

The Bezout converse handles the existing gcd and integer representatives directly. N=1 is included; no primality, field assumption, or inversion of the order of the diamond group is used.

## Exact remaining realization inputs

The final torsor theorem still takes an actual faithfully flat R-algebra S, an actual equivariant splitting S⊗R B ≃ (primitive pairs → S), and the given automorphisms of B. It does not construct the relative primitive-torsion scheme of an elliptic scheme or its geometric splitting, nor does the complex-point result assert such a relative construction. The effective coarse action modulo central ±1 is not asserted here. The actual global refined geometric realization remains unproved.

## Replay

Run `bash primitive-diamond-bridge/build.sh` from the common project root. The script strictly rebuilds this one module against the existing checked dependency cache, then recursively checks the axioms of every declaration originating in the module. It is not a fresh replay of the entire imported closure. The receipt binds exact source, build, and audit output. Allowed axiom roots are only `propext`, `Classical.choice`, and `Quot.sound`.
