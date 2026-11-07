# Actual integral closure of the normalized unit-root cover

Strict kernel replay and exhaustive project-module audit passed: six public theorem declarations in one module, with only propext, Classical.choice and Quot.sound as axiom roots.

For an actual integrally closed base R, actual fraction field K, and actual finite smooth R-algebra S, `smooth_finite_integralClosure` proves Mathlib's actual predicate

    IsIntegralClosure S R (S ⊗[R] K).

It does not assume that S is normal or that its image already is the integral closure. The proof uses Mathlib's proved smooth-base-change theorem for integral closure. The original integral closure of R in K consists of actual images of R; tensor induction shows the entire comparison-map image lies in S. Smoothness supplies comparison-map surjectivity, and flatness proves the actual generic-fiber inclusion injective. Finiteness supplies integrality in the reverse direction.

The actual constructed root algebra R[X]/(X²-u) is finite étale when u and2 are units, so the theorem applies directly, including when u is not a square. A further result proves the same algebra is the integral closure of any actual finite R-order acting compatibly on that generic fiber. The DVR specializations infer integrally closedness automatically, rather than asking for it separately.

## Source boundary

This supplies the actual normalized algebra, not an assumed normality conclusion. To call it the normalization of the specific even-contact equation, the actual contact-order map and its generic-fiber identification still must be joined. The separate base-change/scaling packet addresses those maps. The actual geometric completed local model, its branch coordinate, and the passage to the global curve/stack remain separate. No global geometric realization or FiveContact49Height is asserted.

## Rebuild and library provenance

Run `bash build.sh`. All project compilations use `-Ddebug.skipKernelTC=false`; imported dependency oleans are reused. The exact unchanged official Mathlib `RingTheory/Smooth/IntegralClosure.lean` was also freshly strictly compiled because its olean was absent from the cache. The script repeats that dependency compilation if needed. No Mathlib source was edited. Its actual smooth-base-change theorem is a proved library dependency, not a new axiom or supplied normalization premise.
