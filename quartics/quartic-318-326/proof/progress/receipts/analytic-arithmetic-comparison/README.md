# Actual analytic/arithmetic fiber comparison

This packet bridges the literal integral family `OpenJModel318.integralModel N` to the genuine analytic elliptic curve `ModularWeierstrass318.curve tau`.

## Constructed results

- At each actual upper-half-plane point with j different from 0 and 1728, and every nonzero base-localization level N, construct the ring morphism `OpenJModel318.Base N → ℂ` by the universal property of localization. Its j-coordinate and inverse denominator have the expected actual values.
- Identify the evaluated literal Weierstrass model and prove its algebraic j equals the genuine analytic j. Construct a complex Weierstrass change of variables using the proved equality, then show it is a pure scaling between the two short models.
- Prove directly that coordinate scaling gives an additive bijection of actual elliptic points: the chord, tangent, vertical, and identity cases are all covered. It therefore preserves exact order.
- Transfer the genuine analytic period parametrization to the literal arithmetic fiber. For every positive torsion order M, all points killed by M are obtained, and exact-order-M points are precisely primitive period vectors.
- Combine the relative rank-eight three-torsion algebra's represented equations with the actual exact-order-three point theorem. This yields a named equivalence over every field extension, then a specific equivalence between the literal arithmetic algebra's complex points and genuine primitive order-three periods.
- On this open j-chart, any two permissible scalings differ by a sign, and their actual point maps differ by elliptic negation. They do not differ by an arbitrary eight-point permutation.

The localization level N and torsion order M are independent parameters. The literal finite-etale algebra used in the final comparison has torsion order three.

## Exact boundary

This is a fiberwise comparison for the specified arithmetic model, not a construction of a general-N arithmetic level scheme or a global analytic/algebraic moduli isomorphism. The complex scaling is selected noncanonically. No holomorphic choice in families, global descent of the selected point comparison, compactification over the arithmetic base, PEL identification, or quotient complex atlas is asserted. The exclusions j=0 and j=1728 are actual chart restrictions, not missing cases silently discharged.

The prior actual ΓH compact topological quotient and its genuine j are separate packets. This packet supplies concrete arithmetic-fiber and torsion comparison data needed for a later family/global bridge; it does not assert that bridge as a premise.

## Verification

Run `build-all.sh` while holding the workspace's exclusive compile lock. All six producer modules are replayed sequentially with Lean 4.35.0 and `debug.skipKernelTC=false`. The import-all audit recursively checks every declaration, including private and generated declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

This is an author replay against pinned predecessor and Mathlib caches, not an independent review or a full dependency-closure replay. Mathlib's exact `NormalForms` and `IsomOfJ` dependency sources were built when their cached artifacts were missing.

In particular, the eight nonzero points of the chosen order-three elliptic fiber must not be confused with the effective coarse Γ1(3) j-cover. The central minus identity identifies opposite markings on the analytic quotient. A coarse modular comparison must account for this sign quotient (and the relevant global moduli comparison); the selected scaling does not remove that obligation.
