# Bounded independent review of contact normalization endpoints

Accepted at the exact source hashes in this receipt. This is an independent source and argument review, not a fresh Lean replay, independent reconstruction of all predecessors, or manuscript incorporation. The producers' replay/audit counts remain producer evidence.

## Global relative normalization

`ContactProjectiveModel318` constructs the actual source map into the projective contact line, its exact reciprocal-coordinate factorization, and Mathlib's relative normalization of that map. The source-to-normalization morphism is a dense open immersion by the proved quasi-finite/separated hypotheses. The model is integral and its map to the projective line is integral. An integral morphism is not identified here with a finite morphism, and properness is not claimed. The reuse of a projective-line construction whose module name contains J does not turn the contact coordinate into a modular j-map.

## Fraction fields of the whole infinity orders

`TensorFractionField318` proves a general fraction-field criterion using the actual generic tensor algebra equivalence, injectivity, and explicit localization denominators. `InfinityFractionField318` applies this to the whole infinity order and transports it through the previously reviewed coordinate field equivalence into the original contact field L. `InfinityOpenFractionField318` identifies the entire open order as a localization of the original order and transports its fraction-field structure with the actual embedding. No component selection or hypothesized surjectivity replaces these constructions.

The previously reviewed distinction of the two rational-function variables is preserved. The infinity generic field is degree eight over its u-line, while the original contact field is degree sixteen over its t-line. The new algebra structures use the actual order embedding and do not incorrectly identify the two base embeddings.

## Whole infinity neighborhood normality and integral closure

`InfinityNormalChart318` proves that the localized u-polynomial base is integrally closed. The whole open order is already a finite étale domain over that base, so `SmoothGenericField318.smooth_integrallyClosed` applies. Its full fraction field is the original L under the specified embedding. The final `IsIntegralClosure` proof uses normality for the forward direction and finiteness over the localized u-base for integrality of every image element. Neither normality of the open order nor the final closure identity is supplied as an assumption.

This is integral closure over the localized u-line, not over the reciprocal projective s=1/t line. Finiteness over that reciprocal base, identification with the global normalization chart, global finiteness/properness/smoothness, integral good reduction, and PEL/Jacobian identification remain separate. I found no mathematical scope discrepancy in these three exact packets.

## Checks performed

Read all five target modules, their receipts, the relevant generic-normality predecessor, and the earlier accepted coordinate-field-equivalence review. Checked every source/artifact hash listed in each target receipt's sha256 map. Did not rerun the kernel or recursive axiom audits; reported counts 25, 107, and 45 are the frozen producer results.
