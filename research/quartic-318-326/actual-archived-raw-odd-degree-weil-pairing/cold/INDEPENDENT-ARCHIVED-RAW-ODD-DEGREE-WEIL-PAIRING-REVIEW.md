# Independent review: odd projection degree on the fixed archived raw companion

**Verdict: PASS, mathematical proof only.** Examined the frozen author paper
`NO-ODD-DEGREE-RAW-COMPANION-ON-THE-ARCHIVED-SCALAR.md` with SHA-256
`250cc0092a87521d2ef4773f277a12c77c274172f98a75c30b7dadaa02f4ad3c`,
and its author checksum list
`7eb5d8dc02b10277ddd9a9740f8fbe94e3250e2b6114a52e8c82ed659816499e`.
The author checksum replay passed.

The fixed input, archived scalar, and raw equation agree with the
published variable-first reparametrization. The published residue
at 6551 gives odd valuation of the very same delta. The two root
pairs have distinct quadratic splitting fields, real and imaginary.
The explicit genus-one model has j = 2048/3; non-CM and the nonsplit
twist imply vanishing rational Hom of the two target Jacobians.
Pullback and pushforward are adjoint for the canonical polarizations,
so the two pullback images pair trivially, even on geometric
2-torsion. This does not require either pullback to be injective.

I checked the local divisor calculation for arbitrary fibre
multiplicity: at an odd fibre the sole Weierstrass point contributes
its multiplicity, and at an even fibre the two points contribute
half that multiplicity times the degree-two fibre class. It works
also at source infinity. The even-subset intersection formula agrees
with [Adam Morgan, §8.1](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/plms.70066).
The two independent root swaps make the overlap of the mixed first
root pair and the full second pair equal, modulo 2, to the first
projection degree. Thus a first odd degree would give pairing −1
instead of +1. Swapping the two sides proves the other degree even.

This excludes both cubic strata for two nonconstant rational
parameters over Q on the fixed archived raw surface. It makes no
claim about even-even families, altered scalars or base fields, or a
specialized rational companion point. No native Lean proof or new
arithmetic evaluation is claimed.

Signed: Independent reviewer, 2026-11-22.
