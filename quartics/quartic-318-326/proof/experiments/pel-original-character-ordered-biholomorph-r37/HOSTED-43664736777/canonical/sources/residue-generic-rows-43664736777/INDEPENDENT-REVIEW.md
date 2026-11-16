# Residue generic integer row repair review

PASS for exact source/application review and subsequent per-lane propagation, not Lean acceptance.

Candidate 6661c0021747b309c0f864fe4acf36ed61ac672c6569f082264a9119d0e9a474; predecessor d525eeaebdc49506f2fc71ba7100a82ed2b7d56adc20b8399a07a110de2336ae. Application 6ea351f6a7fa2c0ddfe7f9ea3dbc366c19c5dea90bcffa134d2f4167207e1105; manifest 5b38dc7f07aef033255337104b9edb6c3415aa7f202a6e04026d997a37068f6c. All 15 bindings independently verified.

CORRECTION: the numbered current errors (including line 42) occur inside the INTEGER hrow norm_num/ring calculation, before later modular cast transport. My earlier transport-focused attribution was incomplete. The current source addresses that precise site: each of eight hpoly identities is universal in arbitrary integers a,b, with no ZMod-valued expression in its goal; only afterward is it instantiated at the unchanged integer casts of actual z.val representatives. The lift definition is definitionally the same coefficient combination. All later carrier changes, integer cast transport, 13 closed modular facts, maps and residue_lift statement remain byte-identical. No new global premise or special input is introduced. Existing resource options are unchanged.

Read the full eight-site diff, original product/lift/conjugate/row definitions and nine-clause contract. Independent exact integer coefficient extraction gives rows (3,2),(-4,-3); (4,6),(-6,-8); (-9,0),(0,-4); (15,70),(-21,-97), agreeing with every source hpoly/hrow substitution. This auxiliary arithmetic check is not Lean execution. Both coordinates for every actual prime 2,3,5,7 and arbitrary z remain covered.

Own infinity5 RESULT ebbb365dad62dc8105bb84821bb9365ab6c719372674c0a395d4323973586b9e and intake 6c735f66e2af3e7260e1afb3aa8f92d59463704269e404d1d4d8b1e2df0581f4 are bound. Current residue module still fails; no downstream evaluator/producer has been accepted through this frontier. No modular hcast-only alternative was implemented or reviewed as the fix. Hosted elaboration must still validate generic norm_num/ring and the unchanged subsequent transport. No local Lean was run.
