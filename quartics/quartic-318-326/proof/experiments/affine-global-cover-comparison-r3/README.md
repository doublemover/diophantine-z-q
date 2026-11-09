# Original covering-line comparisons for the global reconstruction

This130-source packet retains the exact127-source `affine-chart-intersection-assembly-r3` closure and adds three connected consumers.

The whole-open pair extension is proved to recover the original supplied pair iso on an affine common open. The matching-family gluing comparisons are then calibrated by the original chart reconstruction paths, and their exact nested-chart compatibility is proved. These specified comparisons construct an actual isomorphism between the pullback of the global base line and the original covering line on the whole inverse image of every original affine base open. Those inverse images form a proved full cover of X.

Every factor of the displayed comparison is explicit: original open pullback/restriction square, calibrated global-to-chart comparison, original affine chart square, original affine reconstruction comparison, original source chart path and original restriction/pullback comparison.

The remaining endpoint is to prove compatibility of these displayed source-open maps, glue them to the global covering-line iso, and verify its original categorical-double square. Local existence alone is not advertised as global effectivity. Non-affine fppf covering sources and represented Picard/Jacobian remain separate.

No local Lean build was run. Hosted elaboration, recursive axiom audit and independent acceptance remain pending. Structural source/dependency checks are not proof acceptance; the accepted progress snapshot remains unchanged.

## Revision after bounded source review

Primary-source preflight finds restrictFunctorCongr is a genuine pushforward comparison, not definitionally eqToIso. Prove its reflexive component equals the original identity using the exact section-map formula, then consume that typed identity in restriction/pullback path normalization instead of unfolding the construction. Hosted validation remains pending.

## Revision after bounded source review

Match the already accepted PullbackOpenFrameNormalization318.restriction_congr reflexive section-map proof, with conditional rfl completion after finite simplification. This handles any remaining definitionally equal identity-map carrier without adding a redundant tactic when simp closes the goal. Hosted validation remains pending.
