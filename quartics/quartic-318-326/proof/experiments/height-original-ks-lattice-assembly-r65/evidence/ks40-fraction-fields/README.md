# Fresh KS40 normalization bootstrap blockers

The exact source-bound hosted union43897325860 passed67 modules and audited1584 declarations. The full64-root gluing closure now passes. Two newly exercised fraction-field producers fail and block the two normalization consumers.

OriginalIntegerFractionField318 lacks the Polynomial namespace opening, so polynomial notation is being elaborated as indexing (including the unknown X error). It also names isLocalization_of_algEquiv in IsLocalization, whereas the pinned theorem is at root. The candidate fixes only that namespace opening and theorem reference.

IntegerPolynomialFractionField318 encounters RatFunc's independently registered scalar action instead of the scalar action attached to the explicit composed fieldAlgebra. The public scalar_tower statement already elaborates using the native action and can use the native RatFunc tower instance. Inside actual_fractionField only, the candidate explicitly selects fieldAlgebra.toSMul and fixes the R,S,A telescope when constructing its algebra-map tower. Its faithfulness proof and descent then use that identical named algebra action. No global instance is removed or replaced, and the algebraMap remains the exact original polynomial coefficient composition.

Only the two failed producers change. Passing gluing76b40ebc and all other sources, including both normalization consumers, are preserved. No resource limit changes, added assumptions, local Lean, or compiler-success assertion. Exact fresh log/inventory/bindings and pinned native sources are included.
