# Original full-overlap composition repair

Base 6b664f8406d512c50432425e3bd616447ff8ad8e, own positive80 run 43655556584. The explicit cover argument now elaborates far enough to leave only two exact presheaf-map composition mismatches. This isolated candidate identifies the composite and direct arrows in the thin category of opens (and its opposite) by Subsingleton.elim before applying functoriality.

1. Required inputs: same arbitrary c:Fin4→Q-units and line sheaf L over the same original projective model. No additional premises.
2. Constructed objects: original finite/infinity full section spaces, overlap, global sections, polynomial localization and actual bases remain unchanged.
3. Coverage: both original whole charts and their entire overlap remain; no restriction to finite-dimensional subspaces or a generic fiber.
4. Transition maps: exactly the native presheaf restriction functor. Composite top-to-chart-to-overlap arrow is equal to direct top-to-overlap because arrows in the opposite opens category are subsingletons.
5. Scalars: no scalar, coordinate normalization, reciprocal-polynomial action or module structure changes.
6. Consumer identity: the equality h is precisely the original direct overlap restriction equality. Two typed hc equalities rewrite the corresponding composed restriction arrows to this same direct arrow after map_comp_apply. Neither transition nor presheaf is replaced.
7. Exceptions: original domains and covers retained. No injectivity assumption added; injectivity of both chart restrictions remains proved earlier in the same source.
8. Dependencies: only two proof sites in global_injective change. Imports, options, declaration statements and every other proof remain byte-identical. Future positive81 successor must retain its own current evidence and all previous unchanged modules.
9. Verification: authentic positive80 failed after 72 successful commands, with this module exit1 in 12.892 seconds at both composition sites. Source review, propagation review and hosted elaboration/audits of this candidate remain pending. No local Lean/Lake, resource/trust change or acceptance claim.
