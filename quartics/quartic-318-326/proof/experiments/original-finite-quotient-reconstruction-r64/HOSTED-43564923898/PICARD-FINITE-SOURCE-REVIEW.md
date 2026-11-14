# Independent source review: Picard canonical affine chart r64

Scope: internal independent source comparison of the frozen candidate below, not Lean/kernel validation or independent acceptance of the arithmetic theorem. No Lean/Lake/compiler/proof build was run.

## Exact evidence

Published base b3d76fb41c03f9194b0613eac0a9b4cb04b2576c; hosted run 43564923898; predecessor original-finite-quotient-reconstruction-r63. Its source and intake were byte-compared with that published Git object. Own RESULT binds intake de679c9068a34d680397aeec51d31abbbb7c6ba5009d35690171fc20d4ff2cd0. RESULT records IntegralBaseReconstruction passing 2.622s and NormalCoverSections passing 2.270s, then CanonicalAffineChart failing 2.371s. These historical successes are not a pass of the candidate.

- Before source: 06abf354b83c78d831446152980aba449c28a89d8705fb38d1a04b29a1b970a5.
- Candidate source: 8bdbf829f824e32abbdde9aa6dd7a8ca970cf5d30dbf78c80500abb895fbd32d.
- Own RESULT: ed588040169d01695883d308254655e30d25ab08fd4e969a495a271e9e3f8dc2.
- Exact failure log: d036d91304e7cc781b82fb159b77726d6ffe46548e74fc401992a1ae85140c58.

## Source/constructed-input comparison

1. The exact first error says pullback.condition is already an equality, not a function accepting two explicit arguments. The candidate supplies its implicit f and g by name: the same JLineAtlas chart at index 1 and the same original p. The equality orientation is fst ≫ chart = snd ≫ p. Left composition by the same isoSpec.inv and the two associativity equations give precisely the unchanged public Cartesian square. No different chart or pullback is substituted.
2. The exact second error is Nonempty of the top-open subtype, required by sections_of_stalks. The existing chart_nonempty p instance already constructs a point of the entire original pullback. The candidate extracts that point and explicitly installs its membership in top. This supplies the missing subtype instance without imposing a new caller premise or restricting to a proper open.
3. The source theorem sections_of_stalks requires an integral scheme, normal stalks at every point, an affine open, and Nonempty of that open. The existing chart_integral, unchanged open_stalk over the original inclusion, isAffineOpen_top, and this exact top witness provide those inputs. The cover remains all original indices i with supremum top, and hnormal remains required at every original cover member.
4. Coefficient ring remains Γ(Chart p, top), with the same Polynomial Q coefficient map obtained from Spec.preimage of isoSpec.inv ≫ projection. No algebra, germ, fraction-field, index or scalar convention is altered.
5. Maps retain direction: original pullback projection to Spec Polynomial Q, inclusion to Y, and canonical isoSpec.inv. The chart maps and coefficient definitions are byte-unchanged. No new scalar or Euler factor is introduced.
6. Downstream OriginalCanonicalAffineReconstruction.canonicalNormal consumes exactly ring_normal p V hcover hnormal. Its original_curve passes the same chart, coefficient and square to OriginalIntegralBaseReconstruction. OriginalSchemeBranchReconstruction.basepoint calculation uses the same square.w. I read these consumers; no isomorphic substitute or pointwise-only normality replaces the whole ring required there.
7. Public theorem signatures, section hypotheses, all exceptional cases and resource/transparency options are unchanged. Changes are confined to two proof bodies; all 79 other root sources in the current 80-source successor are byte-identical to the predecessor.
8. This is a bounded repair of observed elaboration errors, not a new mathematical route or historical whole-proof acceptance. Later consumer elaboration, including hidden-map instance registrations in CanonicalAffineReconstruction, remains untested and unchanged.
9. No source-level blocker was found. The candidate is suitable for its next hosted check, but kernel elaboration and whole-theorem acceptance remain pending. This report does not authorize changed metadata, source or publication; final packet bindings/contract review is separate.
