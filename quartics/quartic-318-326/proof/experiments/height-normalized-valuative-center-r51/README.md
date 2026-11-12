# Exact all-place overlap-map replay

Successor to height-normalized-valuative-center-r50, preserving 95 of its 96 sources exactly. The sole changed theorem proof is actualOverlap_generator in IntegralOverlapRootGenerators318. Its original statement, maps, three generator indices, rootUnit scaling and 1,200,000-heartbeat budget are unchanged.

The a1735 hosted run passed finiteBaseChange_generator and infinityBaseChange_generator, then exhausted whnf at the specialized native_overlap_generator application. This revision names the already-constructed finite, reciprocal and scaling equivalences, separately supplies their existing generator identities, and applies the abstract overlap_value theorem directly. It avoids reconstructing the specialized root-order/tensor-algebra chain while matching the consumer. The same compositional equality is proved; no weaker statement, new hypothesis or axiom is introduced.

The exact tested source, RESULT and failure log are preserved under verification. This is a candidate elaboration repair, not a verified speedup: no local Lean or profiling has been run, and only hosted CI can establish that the same resource budget suffices.

All original all-place model boundaries remain: the original signed-root point has its actual normalized valuative center, but regularity, reduced fibers, comparison with the smooth normalization, global canonical/Hodge lattices, KS210 and archimedean metric inputs are not supplied by this replay. The full original r50 application contract is inherited with the one proof-only change recorded in INHERITANCE. Independent source review and hosted validation remain pending.
