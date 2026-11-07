# Actual Weierstrass analytic local coordinates

This packet proves local complex-analytic chart identities for the actual normalized Weierstrass parametrization used by the preceding additive equivalence.

* At every nonlattice argument, at least one of the actual normalized affine coordinates x or y has nonzero derivative. That coordinate has a genuine analytic inverse, with both neighborhood inverse identities. Both affine coordinates are analytic functions of the selected coordinate.
* At infinity, the actual Laurent expansions construct a filled parameter equal to −x/y on a punctured neighborhood and a filled second projective coordinate equal to 1/y. Both vanish at zero and are analytic there. The first parameter has derivative 2π, hence a genuine analytic local inverse; the second coordinate is analytic in that parameter.

The finite derivative certificate includes zeros of ℘′ and uses the actual nonzero modular discriminant. The infinity denominator is exactly 1−z³℘′Except₀(z)/2, with value 1 at zero. No chart, invertibility or nonzero-derivative premise is supplied by a caller.

## Exact boundary

These are actual analytic coordinate and inverse identities. This packet does not install a topology or a complex-manifold structure on Mathlib's elliptic point type, and does not assert a registered global analytic isomorphism or identify the specified modular family. The previously checked additive equivalence remains the actual underlying point map.

## Reproduce

Run `bash run.sh` from this directory or its parent. Both source modules are rebuilt with strict kernel checking, followed by an exhaustive recursive axiom audit of all declarations belonging to them. Only propext, Classical.choice and Quot.sound are accepted.
