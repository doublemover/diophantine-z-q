# From the original localized module to an actual sheaf frame

`AffineModuleBasisFrame318.frame` uses the actual tilde/global-section counit isomorphism to turn a basis of an affine quasicoherent sheaf's original global-section module into a free-sheaf frame.

`LocalizedModuleSheafFrame318.equiv` compares the canonical localized original global module with the actual global sections after restriction along Spec(R[1/a])→Spec(R). It is built from the original restriction map and the exact open-image comparison. The ring action is the actual localization-ring action; `equiv_mk_one` and both inverse lemmas retain the original map.

`FiniteTargetSheafFrame318.unitFrame` transports this frame to the original open subscheme D(a), using the literal localization Scheme isomorphism and its inclusion square. `exists_frame` combines it with the finite-algebra target-neighborhood theorem: every target point has a principal neighborhood whose entire source preimage trivializes the unchanged original quasicoherent sheaf.

The last theorem still explicitly assumes that the original global section module is finitely presented, flat and rank one at every prime. Removing those hypotheses from genuine covering line frames is the separate affine-line producer. This packet does not claim a Picard norm, cover-independent line-bundle classification, Jacobian, polarization or PEL object.

Three sources strictly pass with kernel typechecking retained; the target-only recursive audit covers all 62 declarations including generated/private declarations. Retained check2 succeeds for the first source before an earlier localization draft fails; check6 succeeds for the final localization source before the open-square draft fails; check7 passes the repaired final open-square source. No failed draft is represented as a final pass. No predecessor/full-chain replay was run.
