# Actual all-place section-to-height bridge

Status: two project modules, 42 recursively audited declarations, strict kernel replay passed. Only standard axiom roots occur.

## Main result

`SectionHeight318.rational_section_height` takes a number field K, actual coordinates a0,a1 in K with a0 nonzero and a1=q*a0 for q in Q, local norms of a rational frame of a metrized line, finite integrality of both sections, and their archimedean norm bounds by C. It proves

    Height.logHeight₁ q <= frame.normalizedDegree + Real.log C.

`section_height` proves the corresponding inequality for the actual `Projectivization.logHeight` of any finite nonzero coordinate tuple, normalized by [K:Q]. Neither result assumes a projective-height estimate, a base-change height equality, or a renamed whole metric-to-height producer.

## Definitions and exact checked steps

- `FrameNorms` consists of positive frame norms at actual `NumberField.InfinitePlace` and `FinitePlace` objects, with finite support of the finite norms away from one.
- `normalizedDegree` is minus the sum of logarithms of frame norms, divided by [K:Q]. Infinite places have the actual multiplicities one or two; finite places use Mathlib's norm-normalized absolute values.
- `logHeight_places` derives the actual all-place formula from Mathlib's multiplicative height. Nonzero tuples, zero individual coordinates, and finite support are checked.
- `section_log_identity` is an exact identity including the finite logarithms of section maxima. Common vertical zeros give nonpositive contributions under finite integrality; no equality at finite places is required.
- `FrameNorms.normalizedDegree_rescale` proves rational-frame independence using the actual NumberField product formula.
- `section_height_relative` and `section_height` sum the local integral/archimedean inequalities and perform the degree normalization.
- `logHeight_ratCast` and `rational_ratio_height` consume the existing `RationalAbsoluteHeight.mulHeight_ratCast`, whose primitive numerator/denominator argument is already checked. Thus the rational contact height is identified with the normalized height over K without any degree bound on K.

No positivity assumption on C is missing: a nonzero tuple at an infinite place and the section bounds force C positive. The proof directly obtains a positive local maximum before applying logarithm monotonicity.

## Geometric boundary

An actual pullback of the bicanonical/Hodge line to an arithmetic point must still supply its frame norms, the identification of its normalized degree with the geometrically defined line degree, and the actual sections and their local bounds. This packet does not construct schemes, stacks, line bundles, arithmetic intersections, or Yuan's isometry. It removes the ordinary all-place section-height comparison and rational height normalization from that remaining geometric application.

For the source metric, the sections are J²q0 and J²q1, their ratio is the rational t, their archimedean norms are bounded by J²*4Cmet, and common vertical zeros are explicitly permitted. The subsequent t/32 scaling and Hodge-degree identification are separate existing steps.

## Replay and dependencies

Run `bash section-height-bridge/run.sh`. It rebuilds both modules and performs an exhaustive recursive axiom audit. The current shared cache lacks Mathlib's `Height.Projectivization` object, so the script first strictly compiles the exact installed Mathlib source in an isolated symlink overlay. It uses the genuine module name and definitions, not a replacement height. The overlay does not alter Mathlib's source or shared cache; generated overlays and object files need not be vendored. Other cached Mathlib dependencies are reused.

The imported project dependency is `converse-work/height-box-interface/RationalAbsoluteHeight.lean`. Its exact source hash and the exact upstream projectivization source hash are recorded in the receipt. All work remains outside the repository; no Git operation was performed.
