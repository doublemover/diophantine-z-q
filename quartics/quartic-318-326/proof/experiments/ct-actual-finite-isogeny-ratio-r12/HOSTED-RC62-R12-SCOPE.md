# RC62 r12: exact reverse Kummer kernel proof repair

R11 exact hosted run 44863381442: 58 of the 62 selected owners compiled; one direct compiler error, three blocked and 42 not selected. 922 declarations audited with no audit failure. Inventory SHA-256 073b333a4450ed8f59c8eadf5afbaee4572bff5ada328d17921cacc19a9b4f57. The prior actual quadratic H¹ module passed.

Only CTActualDualKernelKummer318.lean changes. Replace the raw failing dependent fin_cases/Decidable tactic with the already green ZMod.val_lt/val natCast proof of the same finite disjunction. Fix encode-one by reducing the exact typed conditional with all branches explicit. For scalar extension in the three actual displacement statements/proofs (and action), use the established pinned iff projection ((map_ne_zero ι).mpr h). Same point formulas, exceptional scalar −3n², chosen roots, actual action, local/global restrictions and all theorem signatures mathematically unchanged. The one new proof-only import is the existing core Omega tactic (already used by the selected closure). All 103 other source bytes, order and complete selected dependency list unchanged. First target is CTActualGloballyFiniteIsogenySelmer318.

This is a source-only validation successor, not a hosted result or a rank/parity claim. No execution limits changed.
