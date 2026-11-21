# Diagnostic-only successor to exact old hybrid mean r1

Source predecessor intake e31636867b5094fadab1bdf96abc43b5dedf79bf6970405444d993bf30e8fe57, diagnostic run 44850657236, source snapshot 34f248d3448a961bd7c24a22013520e29ce68592, selection 4b129783… exactly 39. Verified diagnostic compiler result: 5 compiled, 13 direct source errors, 21 blocked by import, 91 not selected, diagnostic audit 50 declarations. This successor addresses the 13 directly diagnosed owners only; all 117 remaining Lean files are byte-exact, including all analytic terminals and unselected owners. No Lean, publish or acceptance claim.

Root causes, grouped by compile fanout:

- ActualPointedCyclicPairing318: expose translation only, preserving existing ring/cyclic API; export-time definitional reduction at two existing theorems.
- ActualTZCanonicalWrapFibres318: pinned Int.emod_add_mul_ediv spelling; explicit inferred DecidableEq I for the two Fintype-of-Pi queries (exact installed consumers already have the same instance). Other fibre/key statements unchanged.
- ActualTZHybridGlobalLocalStencil318: explicit otherwise unobservable s,t for the global needle; prove the local needle's zero affine contribution before unfolding selectors; normalize false=true in the four literal sign cases. Same probes and divisor condition.
- ActualTZContiguousFinInterval318: space the compound binder to prevent inconsistent lexing and normalize the same equality in the orientation actually produced by Finset.sum_bij. Same positive representative.
- ActualTZLiteralWrapClipping318, ActualTZNestedWeightedError318, ActualTZSparseWrapUnion318, ActualTZPrimeSupportCRT318: glued ≤m or <m tokens resolve to Matroid notation in the pinned environment; type/space exactly the intended binders. Clipping also fixes the pinned add-inequality order and parenthesizes the entire summand to retain the necessary wrap multiplicity, and reduces a−a before nonnegativity.
- ActualSmallCoefficientPrimeBudget318: clear the positive divisor on the right, not on the left.
- ActualTZOldProductAverage318: explicit codomain function witness for the existing shared mean permutation.
- ActualTZOneDivisorExpansion318: the literal nonzero integer hypothesis supplied to Nat.mem_divisors; the lcm iff handled by Decidable-aware simp under the four cases (former dependent rw forbidden). Same sum/cutoff.
- ActualTZProductResidueDominance318: explicit nonnegativity and congruent product commutation after dividing by the same denominator.
- ActualTZSignedAxisSupport318: explicit summand on Fin↔range; instead of trying to cast an order proof from ℝ into ℚ≥0, clear positive denominators in ℚ≥0 and invoke the same literal integer interval count: intHits ≤ L/p+1, hence p*intHits ≤ 2L for the long-axis case. No assumption of uniform long residue mass.

Direct-diagnostic owner/source verification is mechanical from exact run INVENTORY, plus original hash before each patch. Every selected dependency and untouched file is checked by regenerated official packet data and byte readback.
