# Actual complete-adic formal evaluation

Two modules, 23 exhaustively audited declarations, strict Lean kernel checking and standard axioms only.

`AdicEvaluation318.eval` constructs a genuine ring homomorphism A[[S]]→R from any coefficient hom A→R and any element of the defining ideal of a complete separated adic target. The coefficient ring receives the discrete uniformity, so no extra continuity, boundedness or characteristic premise is imposed on the coefficient hom.

`CompleteContactEvaluation318.completeEval` derives the actual Hausdorffness and completeness of the ideal-adic topology from Mathlib's algebraic `IsAdicComplete`. Its value on S and on every constant series is proved. `contactEval` specializes to u*pi^(2m), with pi in the ideal and m>0. `actualFormalBaseChange` then tensors the existing actual formal cover using this constructed algebra map and identifies the raw quadratic contact order. There is no supplied formal parameter-map hypothesis. `complete_dvr_map` derives maximal-ideal membership from an actual irreducible uniformizer in an actual complete DVR.

Mixed characteristic is allowed. The positive-contact restriction is essential: at m=0 the parameter is a unit, so arbitrary formal series do not automatically admit evaluation. This packet does not assert the existence of a source coefficient map or of a complete geometric local model, nor identify the source curve with the formal quotient. It supplies the genuine evaluation construction once those actual objects are present.

Replay: `bash run.sh`. The pinned Mathlib power-series evaluation and algebraic/topological adic-completeness APIs are used directly. Generated compiler objects are not deliverables.
