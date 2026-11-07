# Actual algebraic horizontal section coefficients

Strict kernel checking proves 32 public theorems in four modules (40 audited
declarations). The source contacts are exactly 0,32,76832,−343 and J is exactly
2765952000. No holomorphy, denominator-unit, derivative formula, cancellation,
local section-integrality or no-common-zero conclusion is assumed.

1. `AlgebraicSectionPullback318` derives the actual polynomial pullbacks and
   applies the laws of a genuine relative derivation to t=a_i+z² and t=1/z².
   It proves the cancellation formulas for (Dt)²/P(t) and t(Dt)²/P(t), including
   the z² zero of the first infinity coefficient. Both a general Dz factor
   and the exact normalized Dz=1 coordinate form are supplied.
2. `HorizontalIntegralCharts318` works in an actual Q-algebra local ring.
   Distinct rational contacts are units, and an actual parameter in the
   maximal ideal has residue zero. These facts derive every finite-branch
   denominator unit. Every infinity denominator factor has residue one.
   The coefficients lift to the local ring, and the first coefficient is a
   unit in the regular/finite branch charts, the second at infinity. This is
   actual algebraic no-common-zero data. The ordinary chart uses actual
   residue separation from all four contacts.
3. `SourceHorizontalSections318` proves that multiplication by literal J²
   preserves these results, since J is a nonzero rational and hence a unit
   horizontally. Its final outputs use the exact source `section0/section1`
   definitions also consumed by the vertical packet.
4. `UnitFrameHorizontal318` removes the need to globally normalize Dz=1.
   An actual unit coefficient of dz in any integral differential frame
   rescales both quadratic coefficients by the square of that unit. All
   three horizontal chart types give the literal J²-scaled sections and a
   unit among their two coefficients.

## Remaining geometric boundary

The actual local ring, fraction field, parameter, rational function equation,
and differential frame must be realized in the source curve/model. In the
arbitrary-frame wrapper, `D(z)` is identified with an actual unit of the local
ring, not assumed equal to a final section value. At infinity/finite branch,
z is nonzero in the fraction field and lies in the maximal ideal. The formulas
alone do not construct these coordinates, a curve atlas, a line bundle or
its overlap identifications. Affine codimension-one extension and global
line-bundle/sheaf/stack realization are distinct subsequent steps.

## Replay

Run `bash verify.sh` with the project's Lean4.35.0 and pinned Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679. Every module uses
`debug.skipKernelTC=false`. The recursive audit permits only propext,
Classical.choice and Quot.sound. Frozen dependencies are vertical-derivation
and vertical-section-integrality; no repository or Git state was changed.
