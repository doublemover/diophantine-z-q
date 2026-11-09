# Actual affine section rings and functorial reduced-unit logarithms

This105-source candidate copies exact relative99r2 and adds six connected
sources. No local Lean build was run. Hosted elaboration and independent
acceptance remain pending. Static checks are not Lean proof validation.

SquareZeroRingLift318 constructs the literal ring map (a,b) to f(a)+epsilon*f(b)
for a specified original ring homomorphism and square-zero element. It proves
multiplicativity using epsilon squared equals zero and provides the functorial
dual extension of an actual ring equivalence.

OriginalDualSectionLift318 applies this to the ORIGINAL first-projection map
on global sections and the ORIGINAL epsilon section pulled from the second
projection. This canonical map is defined before choosing any affine model.
Its reduction is proved to be the first coordinate, and naturality under the
actual thickened original scheme map uses BOTH original projection squares.

OriginalAffineDualSections318 takes Spec S over Spec R and compares that SAME
canonical map with the actual tensor/dual algebra inverse. Its coordinate
map is the original affineIso inverse on Gamma followed by the original
Gamma-Spec isomorphism. Separate calculations fix coefficients from the first
projection and epsilon from the second. Pinned Gamma-Spec naturality retains
the original ring maps. The comparison proves canonical-map bijectivity,
not merely existence of an unrelated section-ring isomorphism.

OriginalAffineDualSectionEquivalence318 transfers this exact canonical-map
bijectivity to EVERY original affine X and original morphism p to Spec R,
using the original scheme isomorphism, actual thickened map and their actual
Gamma maps. Its inverse first coordinate is proved to be the original
zero-section map on global sections. No nonempty or field assumption is used.

OriginalAffineUnitLogarithm318 now gives every actual unit reducing to1 a
UNIQUE original coefficient. The exponential is proved to equal the earlier
actual infinitesimal unit1+epsilon*pi-star(a), not a fresh class label. Both
inverse identities, uniqueness, addition/multiplication and additive logarithm
of multiplication are proved on the entire original reduced-unit kernel.

OriginalAffineLogarithmNaturality318 proves exponential and logarithm commute
with the ACTUAL original scheme map on both thickenings and coefficients.
The complete multiplicative transition equation is equivalent to its additive
equation with those same maps. No replacement of restriction maps by an
unidentified coordinate homomorphism is permitted.

Remaining: apply these logarithms to the actual pointed frames on whole
thickened cover opens, identify every resulting cocycle with original H1 and
prove the inverse classification, then compare actual norm with trace. This
packet supplies the ring/unit join but does not claim whole-H1 classification,
represented Picard/Jacobian geometry or an isogeny.

Revision2: reviewer preflight flagged terminal normalization tails after rw
that may already discharge goals under definitional reduction. Add all_goals
guards to the actual-section naturality final simp and both Gamma-Spec inverse
cancellation tails. No hypothesis, statement, map, normalization or consumer
changes.103 source files remain byte-identical to105r1. This is preflight
robustness, not a hosted failure or a claim of Lean validation.

Revision3 preserves the a51868a hosted failure. The original positive edge now
explicitly uses identity restriction on U intersection V and the given h.
The reverse edge explicitly names EVERY restriction domain and inclusion,
then applies the original restriction composition and additive group identity.
This does not change either transition, the original gauge, or its sign.
All104 other sources exact105r2. Hosted elaboration remains pending.
