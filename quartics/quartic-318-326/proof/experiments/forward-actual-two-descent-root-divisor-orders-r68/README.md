# Constructive split-prime native API repairs

Fresh split-prime run43938887239 preserved the checked norm-division dependency and audited3 declarations. SqrtTwoSplitPrime318 failed at five proof/API sites: integer-to-residue casting, addition ordering in a coordinate, natural absolute-value casting, a nonexistent measure_wf name and unfolding the evaluation map.

Use congrArg for the integer cast, addition AC normalization, explicit Nat.cast_lt and Int.natCast_natAbs, native (measure f).wf.has_min, and simplification of the actual lift and local element. The mathematical statements, hypotheses, definitions, imports, options and resource limits remain unchanged.

All1327 other source bytes and1328-root order are retained, including all120 checked arithmetic modules,11 pure modules, both checked norm ingredients and the separate67 finite-index repair. The norm-sufficiency draft remains excluded. Targeted split-prime closure remains exactly2 roots. No local Lean, full norm criterion, auxiliary-value selection, local-global or simultaneous-twist claim is made. Strict hosted compilation/audit of the repaired leaf remain required.
