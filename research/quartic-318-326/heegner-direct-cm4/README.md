# Exact fixed-level CM4 Heegner trace controls at 53

This directory gives a source-only replay of the direct conductor-four construction on the fixed degree-two quotient of X₀(48). The starting case is d=323 with one 24-mark oriented CM orbit. Its genuine full ordinary Hilbert trace is certified nontorsion by its order-13 reduction at 53. Three bounded companion controls use the same construction.

| Substitute last prime | d | Raw ring residue | Ordinary Hilbert residue | Order-13 image on E_d(F₅₃) |
|---:|---:|---:|---:|---|
| 19 | 323 | 9 | 11 | (42,11) |
| 19 | 132107 | 1 | 7 | (24,31) |
| 67 | 1139 | 11 | 12 | (11,46) |
| 67 | 465851 | 7 | 10 | (44,51) |

These are two **substitute-scalar** paired controls with β=17 and θ=409. Neither is a numerical pair of the actual fixed production scalar. The exact ray, unknown companion support and full nonvanishing for the genuine production pair remain separate. The tested direct norm-shell method cannot simply be enlarged to production: the smaller genuine base trial alone has over 201 trillion slices in this implementation. The exact costs are in the calibration report and JSON, not a claim about all possible algorithms.

## What's here

- [CM4 and Hilbert descent](foundations/DIRECT-CONDUCTOR-FOUR-HEEGNER-TRACE.md), [exact Hilbert descent](foundations/EXACT-HILBERT-DESCENT-OF-THE-LOW-MARK.md), and their [independent mathematical review](foundations/INDEPENDENT-FOUNDATIONS-REVIEW.md).
- [Finite calibration](calibration/DIRECT-CM4-F53-CALIBRATION.md), with all 24 exact rows at d=323 and exact full-row hashes and all-orientation counts at the other three.
- [Independent review and projective replay](independent/INDEPENDENT-REVIEW.md), which verifies the literal full group sums from the low-level chart values. The ring-to-Hilbert factor is removed only in the actual order-13 line.
- [Fixed ternary coset coefficient target](coset-theta/FIXED-UNIVERSAL-TERNARY-COSET-TRACE.md), a separate mathematical reduction for subsequent work. It specifies the same trace coefficient at address 4d of one fixed unweighted modular series. It is not a fast coefficient extractor or a theorem that both target coefficients are nonzero.
- Byte-exact donor norm and chart books for the same 416 marked supersingular labels, and the exact Eisenstein norm sieve, under donors/.

## Reproduce

From this directory in a Linux shell with Python 3 and coreutils:

~~~sh
sh replay.sh
~~~

The replay verifies every file against SHA256SUMS, reruns all four tiny exact embedding enumerations, and compares the independent projective arithmetic, production-size arithmetic and trace-zero lattice controls. All inputs are relative to this directory. No network, Lean, PARI, large production enumeration, archive extraction, or compiled dependency is used.
