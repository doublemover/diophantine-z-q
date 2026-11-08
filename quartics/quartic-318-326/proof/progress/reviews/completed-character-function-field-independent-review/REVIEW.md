# Bounded actual completed-target function-field review

Reviewer: /root/restart_checkpoint. Producer: /root/restart_contact_field. Decision: accept the two exact source modules and their stated whole-target-field comparison. This is a non-author source/application read, not a fresh Lean replay or a whole geometric realization acceptance. I previously integrated and reviewed completed-map predecessors; I did not author these source proofs.

## Actual maps and inverse witnesses

ActualOpenFractionField318 uses the actual generic-stalk map of an open immersion. OpenFunctionField318.fieldIso explicitly composes transport to the image generic point with the invertible open-immersion stalk map. The coefficient algebra on the target generic stalk is the inverse of that very map composed with the affine coefficient germ. genericAlgEquiv proves its coefficient identity by apply_symm_apply, then transports the existing affine IsFractionRing instance. IsLocalization.algEquiv supplies both inverse laws and fixes all coefficients, not just cardinality or selected generators.

The pinned Mathlib FunctionField implementation defines this function field as the generic-point stalk. Its affine fraction-ring instance uses localization at the zero prime of the domain, and its open-immersion generic-point theorem uses actual irreducibility and nonempty source. IsIntegral and IsDomain in the generic packet supply those hypotheses; an empty affine open is not silently accepted. The generic_germ endpoint is the precise square on every open whose source and preimage section domains are nonempty.

CompletedCharacterFunctionField318 applies this to the actual finiteChart of each literal completed published model. Target integrality is supplied by the previously checked actual completed target. The affine order is exactly PublishedCharacterFraction318.Order, with its domain proved by the existing injective embedding. The destination is its already specified entire character subfield of the original contact field, and actual_fractionField uses the literal cubic/published coordinate equivalence, not an independently selected isomorphic field. characterEquiv_on_order fixes every element of that order. originalEmbedding is the same character-subfield inclusion composed with that equivalence, with originalEmbedding_on_order retaining the earlier actual embedding. finite_germ separately binds the geometric open-stalk origin of the coefficient algebra.

## Nine application obligations

1. Source hypotheses: actual integral target, domain affine chart and open immersion are explicit.
2. Constructed object: scheme generic stalk, not an abstract named field.
3. Domain: all i : Fin 4 with the fixed original rational twists; entire coordinate ring and entire character field.
4. Comparisons: actual open generic-stalk isomorphism and genuine localization equivalence, each with inverse laws.
5. Consumer identity: same literal target, published order and original character subfield.
6. Coefficients: explicit local Algebra instance and equality for every order element; no unnoticed scalar twist.
7. Local conditions: generic-germ theorem retains both nonemptiness premises.
8. Exceptions: nonsingular/integral targets and original unit twists are retained; no extra generic-point choice.
9. Downstream: the completedMap generic pullback, its degree or finiteness, comparison to the earlier relative normalization, and Jacobian/PEL statements remain separate.

## Evidence and limitations

Every producer artifact, stated dependency and predecessor receipt hash was recomputed. check-20 honestly contains the passing generic module and an earlier failing concrete draft. check-21 is the successful concrete check. Neither log is represented as a combined recursive audit. That audit and integrated hosted verification remain pending. No additional compiler run was performed for this review. The current README and application do not overstate the result.
