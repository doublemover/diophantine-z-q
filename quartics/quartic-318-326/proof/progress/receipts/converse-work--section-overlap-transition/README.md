# Actual quadratic frame and overlap transition

Seven public theorems and one constructed linear equivalence pass strict kernel
checking. Actual scalar multiplication of a genuine relative derivation
produces the exact quadratic transformation of the two literal source section
coefficients. `frameChange` is an actual linear equivalence of a coefficient
pair over the overlap ring, given by the square of a unit, and has proved
identity, composition and inverse laws.

`overlap_pair` works with an actual algebra tower A→C→K, where K is the actual
fraction field of C. If two independently extended affine pairs represent the
rational sections in frames related by the actual derivation scaling, then
the second pair is exactly the square-unit transform of the restriction of
the first. The proof uses fraction-field injectivity, not an assumed overlap
compatibility conclusion. No height or valuation estimate is an input.

The statement is conditional on the source affine rings, their actual overlap
maps, and their frame identification with the actual bicanonical bundle. It
does not manufacture a global atlas, line bundle, stack, or its sheaf descent.
The transition factor is the scale of the dual derivation; the cotangent
frame scales inversely. This fixes the direction without silently changing
coordinate conventions.

Reproduce with `bash verify.sh`: Lean4.35.0 and pinned Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false, recursive
standard-axiom audit of all8 declarations. No repository/Git or frozen input
was changed.
