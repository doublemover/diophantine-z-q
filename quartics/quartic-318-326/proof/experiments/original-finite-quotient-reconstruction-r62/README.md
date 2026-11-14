# original-finite-quotient-reconstruction-r62

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent application acceptance or full theorem claim.

Revision of `original-finite-quotient-reconstruction-r61` at `a2d615a4183174328321ea21d60879add229de3a`.

Prove reducedness through a kernel-visible local copy of the exact original two-polynomial-chart cover, without changing the accepted atlas baseline.

## Objects

The base remains ProjectiveJLine318.scheme Q. The local OpenCover C has exactly the original JLineAtlas.cover components: index Fin 2, each object Spec(Polynomial Q), and map JLineAtlas.chart Q j. Only the cover structure is reassembled locally so the fiber projections are kernel-visible; no replacement projective scheme or affine surrogate is selected.

## Coefficients

Both original polynomial charts are over Q with their unchanged JLineAtlas.chart coordinate maps. Each chart is reduced by the native Spec reducedness instance for Polynomial Q. No abstract reducedness or integrality hypothesis is added to the base.

## Exact maps

The maps C.f are literally JLineAtlas.chart Q, preserving the original dehomogenization maps and open immersions. Coverage uses the same standard_opens_cover and chart_range: every projective point lies in some original coordinate basic open, hence in the range of its original chart map. The quotient p and its dominant/integral assumptions in the final integral theorem are untouched.

## Diagnosis and proof route

Hosted CartesianNormalChart318 and CartesianCurveReconstruction318 pass. The next reducedness proof fails kernel type checking because ordinary baseline JLineAtlas.cover is not exposed: the proposed uniform Spec reducedness lambda cannot be converted to its hidden cover.X fibers. Baseline files remain immutable. A local explicit cover with identical Fin2/chart components and full original coverage makes the dependent family genuinely reduce to Spec(Polynomial Q). Pinned Mathlib IsReduced.of_openCover requires an actual open cover and reducedness at every fiber; these are now supplied explicitly. The final integral theorem still obtains irreducibility from the original dominant integral quotient and combines it with this independently derived reducedness.

## Full coverage

All Fin2 indices and every point of the original projective scheme are covered by the original standard coordinate opens. The native coverage proof extracts j and an actual chart preimage q for every base point. No index is omitted, no chart is shrunk and no coverage assumption is substituted for the proof.

## Local hypotheses

Original quotient hypotheses IsIntegral Y, IsDominant p and IsIntegralHom p are unchanged. The same reducedness and irreducibility theorem is applied to the same base. No baseline hash, import/order, budget, trust setting or public theorem statement changes.

## Downstream

OriginalIntegralBaseReconstruction318 and later normal-cover/canonical-affine-chart modules continue to receive IsIntegral for the same original projective base through the unchanged integral theorem. Successful preceding Cartesian sources remain byte-identical.

## Evidence and limits

Exact hosted failure, result, before source and bounded patch are retained. Every other root Lean file is byte-identical to its published predecessor. No imports/order, resource limits, admitted axioms, baseline or cache policy changes. Source review and structural checks are not Lean passes. Hosted strict compilation, recursive axiom audit and later-module checks remain pending.

Pinned primary Mathlib source: commit 56a005855ea17e0b0958f73ec801ae140b0a1679, Mathlib/AlgebraicGeometry/Properties.lean, IsReduced.of_openCover. Baseline JLineAtlas318 and ProjectiveJLine318 exact source copies are evidence only, not shadow modules or edits to accepted baseline.
