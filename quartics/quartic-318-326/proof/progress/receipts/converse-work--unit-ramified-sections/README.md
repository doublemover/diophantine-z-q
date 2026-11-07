# Unit-twisted horizontal ramification in the original local ring

The 14 public theorems in two modules (21 audited declarations) remove the need
to take a square root of a local ramification unit. Exact square coordinates
need not exist in the original height-one localization; the actual source
ramification index two gives `t−a=u*z²` or `1/t=u*z²`, with u a unit.

`UnitRamifiedPullback318` proves the genuine relative-derivation identity
D(u*z²)=z*(z*D(u)+2u*D(z)), the actual polynomial pullbacks, and the exact two
rational section coefficients for both coordinate equations. Cancellation is
proved, not assumed. `UnitRamifiedIntegral318` uses the actual residue field
of a Q-algebra local ring: z has residue zero, u and D(z) have unit residues,
and D(u) is integral. Therefore the parenthesized factor is a unit. The actual
finite-branch denominator factors are units by distinct rational contacts;
the infinity factors have residue one. Both exact J² source sections belong
to the original ring and one coefficient is a unit. No unit square root,
henselization or extension field is required.

Remaining inputs are actual local ring/fraction-field/coordinate/frame
realization, u and the dz coefficient being units, and preservation of the
local ring by the genuine relative derivation. The exact coordinate equations
are retained. These are geometric/frame data, not the desired integrality or
no-common-zero conclusion. Global affine/sheaf realization is separate.

Run `bash verify.sh`. Lean4.35.0, pinned Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679, strict kernel checking, and recursive
standard-axiom audit are recorded. No frozen dependency, repository file or
Git state was changed.
