# Whole original contact source: smooth branch cover

Fresh strict replay and recursive axiom audit passed: 103 declarations in five
modules. Only propext, Classical.choice, and Quot.sound are permitted.

This packet works with the exact original four-root polynomial order
`ContactKummerOrder318.SourceOrder c`, retaining arbitrary nonzero rational
squareclass twists `c : Fin 4 → ℚˣ`.

The four actual three-other-contact denominators span the unit ideal by an
explicit Lagrange partition at 0, 32, 76832, and -343. Each principal open is
identified with the whole existing finite-branch chart, not a selected
component. The whole-source smoothness proof descends smoothness
from these four charts over ℚ. Each branch base is literally a polynomial
root coordinate, its open is a localization, and the full branch algebra is
finite étale over that open.

A separate branch-normality endpoint proves normality of those entire
principal opens. Whole-source normality descent and the actual global
normalization t-chart identification are coordinated in a separate packet.

This does not claim étaleness over ℚ[t] at ramification, global smoothness of
the projective normalization by itself, a global elliptic multiplication
kernel, general-level torsion, a PEL/Shimura identification, or the final
Diophantine theorem.

## Exact endpoints

- `SourceDenominatorCover318.span_top` proves the four actual denominators
  span the unit ideal, using the checked literal polynomial identity `unity`.
- `SourceBranchLocalization318.sourceLocalizationEquiv` is the actual
  rational algebra equivalence from each principal localization to the whole
  branch order; `sourceLocalizationEquiv_on_source` and
  `sourceMap_on_polynomial` record compatibility with the source and its
  original polynomial coordinate.
- `SourceGlobalSmooth318.source_smooth` proves
  `Algebra.Smooth ℚ (ContactKummerOrder318.SourceOrder c)`.
- `SourceBranchNormal318.localized_integrallyClosed` proves normality of
  each entire principal localization for the independent global descent.

The earlier frozen `SourceNormalChart318.source_integrallyClosed` only
proves normality of the unbranched source open. It is not used as if it
already proved normality of the whole unlocalized source.
