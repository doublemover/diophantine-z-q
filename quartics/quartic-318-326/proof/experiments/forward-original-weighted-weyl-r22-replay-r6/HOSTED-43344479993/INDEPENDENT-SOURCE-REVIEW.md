# Independent internal source review: arithmetic successors

Reviewer: PEL repair worker, distinct from the arithmetic repair author.
Scope: source-level comparison of the exact failing hosted logs, before/after sources, the source theorem requirements, aliases, and downstream carriers. This is not Lean verification, external review, or arithmetic theorem acceptance.

## Findings

- Detector repair: the hosted residual goals are precisely pre 190/241/292 = witness q labels h t 190/241/292, and pre is the local let-binding of that same witness. Adding pre to the existing simp set exposes only that binding. All three Fin 3 cases remain covered. The rational parameters, stored pole indices, certificate arguments, and first263 consumer are unchanged. The two successor detector sources are byte-identical.
- Positive-generators repair: the proof specializes the existing abstract coordinate_transport lemma to the original finite and infinity section modules, their actual Laurent common module, and the actual polynomial-basis coordinate equivalences. Unfolding coordinates, rawTransition, and ContactCommonLaurentModule318.transition exposes exactly the abstract lemma composition, with the infinity-to-common recovery followed by inverse finite recovery. The reciprocal map is still u ↦ T⁻¹. No rank-only replacement, field change, new hypothesis, resource change, or statement weakening was introduced.
- The source-level changes are justified. The simpa specialization may still encounter an elaboration/resource limit; only hosted Lean can decide that. No kernel pass or complete packet pass is asserted.

## Reviewed exact sources

- `forward-original-weighted-weyl-r22-replay-r3/ThreeDetectorUniformFamily318.lean`: SHA-256 `df9f80935c672c24ed8d095be490c4253951c69af224fbf8236d9d54737fe42b`.
- `forward-actual-two-descent-root-divisor-orders-r3/ThreeDetectorUniformFamily318.lean`: SHA-256 `df9f80935c672c24ed8d095be490c4253951c69af224fbf8236d9d54737fe42b`.
- `contact-original-positive-generators-r64/ContactOriginalRestrictionCoordinates318.lean`: SHA-256 `a3579fed97b758be6d0f3199b851d553911fd7475112810cfcfd8628de1ff3b3`.
