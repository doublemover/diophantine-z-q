# Independent source review: first two PEL candidates, run 43539970197

Published head: 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. Disposition: no source-level blocker found in these exact bounded edits. No Lean/Lake was run. Hosted compilation/declaration auditing remain required; neither candidate nor whole packet is accepted by this source review.

## Actual polarization transitions

Before 28cd8dc60e22245a967dedb6920d2b0700d2c955dc72f43efef42374898d9fbf; after ab34bd2d8e239908e60e28c906bb4542961efb39138071e59334816dd8e18f74. Own torsion-r14 artifact 14091885964, log 4a0dba8fe26ac310b90ac58fa75eedbfab625a97243f6a52f41672e70e747484; failed module time 1.467 seconds.

Read full before/after, exact log, application comparison and native PELOriginalPeriodLattice lattice/exact_period_subgroup definitions. The added change expresses membership in the additive subgroup of the same integer submodule. It does not replace that lattice: exact_period_subgroup already identifies exactly this subgroup with the actual original period subgroup. The subsequent quotient calculation and covering sections remain unchanged.

Classical decidability is installed only in the pre-existing noncomputable shift definition. The exact dependent if and both branches remain: the difference of the original two local lifts on their full true overlap, and zero outside it. No new typeclass premise, chart domain or selected component is introduced. The final eventually-equal argument uses he rather than he.symm, which is the orientation explicitly required by the hosted diagnostic: the desired shift-valued function is on the left and the continuous chart difference on the right. This preserves the lattice shift, local constancy and original polarization factor/cocycle/continuity statements.

The later shift warnings and goals in the old log are downstream of its failed decidability synthesis; source review does not assert that all later checks now pass. Prior chart/instance/API errors disappeared in this hosted run, but this module still failed.

## Actual finite/infinity coordinate overlap

Before e592d2e592f0bffd4447b15ede252cc0ee4c8e5d2fe693f81215fbce2b1ff5af; after 72f61d6107fefca5b7695c9ea0e6bc1d5d944e0f7519722f87d33c524ea1cee9. Own cotangent-r40 artifact 14091187857, log c0e871a22886afa3a46be2dcade1cbde05c9fc7ced31ec10dd1686e416ff79e0; failed module time 9.389 seconds.

The entire diff is one inserted colon in the calc justification `_ = z b 0^2 * zi b^2 + _ := by rw [finite_relation]`. Exact log reports an unexpected equals token where := is required, followed by the placeholder/unsolved calc fallout. This is the correct Lean calc syntax. The algebraic step uses the exact zeroth root relation z0²=t-b0, then z0*zi=1; it proves the same normalized infinity relation for every k. All four root ratios, distinguished root0, s0=1, both specified principal localizations, forward/reverse algebra maps and inverse identities remain byte-identical. No quotient, field, radical, open subset or map is substituted.

The preceding FourRootInfinityCoordinateRing318 did pass hosted Lean in this exact artifact (2.871 seconds); that is individual module evidence, not packet success. This syntax candidate itself is not yet hosted-checked.

## Provenance and contract checks

Both before sources exactly match their own published predecessor root files. Recomputed before/after/log hashes match FIRST-TWO-MANIFEST.json. Each own RESULT carries the exact own predecessor intake hash; files were read directly from the saved hosted artifact extraction. No imports, public declaration signatures, hypotheses, resource options, trust flags or admissions change. Read the full application comparison: it identifies the original objects/maps and preserves their full domains rather than weakening to a generic or restricted case. Exact-copy propagation must later be reviewed independently against each applicable predecessor.

FIRST-TWO-APPLICATION.md SHA256: 7938e5445a51b33ebcae8ac9677515f5c216f2bf01d88befa38a741999e1f64a
FIRST-TWO-MANIFEST.json SHA256: 9af010f6db0b0e36daeb9e1152899d7a9a1805c1b2627b57d6fe4c0e00976635
