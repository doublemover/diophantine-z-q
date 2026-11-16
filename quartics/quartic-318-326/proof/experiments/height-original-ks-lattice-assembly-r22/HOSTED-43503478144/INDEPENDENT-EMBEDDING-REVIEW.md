# Independent bounded source review: native open carrier

Reviewer: lean_review_resume, distinct from geometry_repair_resume. Evidence: run43503478144 at head56773da3e1a8045d885059ae17053fcbf0af6067.

Source before SHA256: a3286e4829e0a388ef00169d4bdfb1d571effc6f89950b919a3b0961fec35970.
Candidate SHA256: 63f6f6af1bf2e0beb927eef8833ecf80476b1c43de4cf9d0dc1d4e17c6276a84.

Read exact hosted error at61:66, exact one-line before/after diff, surrounding localization-equivalence range proof, and pinned Mathlib Topology/Sets/Opens. The native Opens structure has carrier : Set alpha and its SetLike instance is defined by coe := Opens.carrier. Thus U.carrier computes the intended underlying set directly and avoids the unresolved Set target of the prior coercion.

The congrArg still transports exactly opensRange_comp_of_isIso for the same Spec of the ring equivalence followed by the same tensor includeRight map. Its result is composed with the same localization_away_comap_range equality. No chart, denominator, scalar action, open subset, source/target ring, public declaration, hypothesis, quantifier, resource option or downstream consumer changes. The single corrected expression is a projection of the same open, not an assumption of range equality.

No source-level blocker found. Suitable for hosted replay only. No local Lean/Lake execution or push; actual elaboration, kernel checking, recursive axiom audit and later consumers remain pending. This is not whole-argument acceptance. Scope is this one source candidate, not successor-folder propagation that has not yet been provided.
