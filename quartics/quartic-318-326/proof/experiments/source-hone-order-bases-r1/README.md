# Explicit monomial bases for the original source-H1 coordinate rings

This two-source continuation is uncompiled. Hosted strict Lean checking, recursive
axiom auditing and independent acceptance remain pending. No local Lean run or
H1 dimension/spanning result is claimed. It depends only on existing baseline
sources, independently of the pending H1 quotient packets.

`RootOrderMonomialBasis318` transports the pinned quadratic algebra basis
`(1, omega)` through the already proved `QuadraticPresentation318.presentationEquiv`.
Tensoring those actual bases gives all sixteen monomials of the original four-root
order and all eight monomials of the original three-root order. The basis entries
are identified with the existing named root generators, not chosen abstract free
bases. Exact coefficient-change theorems preserve each monomial.

`ContactHOneOrderBases318` specializes these constructions to:

- the original finite order over Q[t];
- the original overlap order over its original localization of Q[t];
- the original infinity order over its original localization of Q[u].

The original finite-to-overlap localization map preserves each basis entry.
Every element has its full finite coefficient expansion. Each infinity basis
entry embeds as the exact product of the original root ratios in the original
contact function field, with scalar one. The actual rings and field are unchanged.

These are coefficient-ring module bases, **not rational bases of H1**. The next
calculation must still reduce overlap coefficients modulo the two original chart
images and prove which resulting classes survive. The expected five classes
(four triple-root monomials/t and the full-root monomial/t) are a working target,
not a theorem of this packet. Their independence, spanning and identity with the
five original quotient-H1 pullbacks remain to be established.

The producer inspected the pinned Mathlib quadratic-basis and tensor-basis APIs
at `56a005855ea17e0b0958f73ec801ae140b0a1679`. Tensor-algebra versus tensor-module
instance alignment and monomial simplification remain elaboration risks until CI
checks the sources. No earlier source, receipt or accepted manifest is changed.
