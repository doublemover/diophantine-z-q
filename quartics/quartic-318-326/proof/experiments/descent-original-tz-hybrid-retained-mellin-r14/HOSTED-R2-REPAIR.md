# Diagnostic-only mean r3

Exact r2 intake 3d226b0e2569b449e9d0aef8b8974038ced6a2a94710a73e26745c2a8ee815a2, run 44852495657. On the same selected 39 modules: 18 compiled, 6 direct roots, 15 blocked, 91 not selected, 215 declarations audited. Applies exactly the six direct source repairs with 124 peer Lean files byte-identical and no import graph change.

- CanonicalWrapFibres: final Nat cardinal reduction now uses the normal simp set (including the Nat scalar identity), not the restrictive residual cast.
- HeterogeneousGridRoots: NNrat order nonnegativity is explicit (the current zero_le is not a function).
- MultiDivisorExpansion: two explicit, typed Finset.sum_coe_sort transports into the literal squarefree subtype univ; use mul_pow in exact two-factor normalization.
- MultiLinearCRT: two remaining glued '<m' tokens corrected; unfold the dependent local roots choice using simp; compare each side of the actual interval-count characteristic function via if_pos/if_neg, not by changing the predicate underneath the specific Decidable instance.
- TwoBlockCoefficients: explicit shared proof-unfolding of both coefficient and translated-structure definitions, instead of relying on exported rfl; space the '<=' before the axis variable, which otherwise parsed as an InitialSeg notation.
- WeightedAxisSplit: give the exact record-level integrand to nested averaging explicitly, instead of letting a higher-order rewrite guess separate two variable dependencies.

No Lean or remote action on these candidate bytes, and no new proof acceptance claim. Use the unchanged intended 39 module selection to expose the next dependency layer, or the smaller six-direct-owner diagnostic closure for backstop.
