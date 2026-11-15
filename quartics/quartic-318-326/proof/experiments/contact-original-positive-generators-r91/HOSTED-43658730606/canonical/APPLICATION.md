# Actual degree-zero rational carrier repair

Candidate authored by independent reviewer for separate arithmetic-owner review. No local Lean/Lake, no active edit or kernel acceptance.

1. Inputs: same original c, same arbitrary original Line L, same genuine derived Sheaf.H carrier. No new hypotheses.
2. Objects: degreeZeroLinear still uses exactly native Sheaf.H.equiv₀. Its additive-equivalence codomain is explicitly typed as the original whole module sections Γ(L.object,top) BEFORE conversion to a rational linear map.
3. Domain: every degree-zero cohomology class and all original line sheaves; no coordinate subspace or selected frame.
4. Map: toRatLinearMap retains the additive map definitionally. The following injectivity proof explicitly changes to this same native additive equivalence, not a new map.
5. Scalars: existing cohomologyModule and sectionModule are unchanged. No Module is manufactured by transporting along e; explicit codomain enables the already registered rational section action to synthesize. Rational linearity of an additive map between rational modules is the pinned native theorem.
6. Consumer: finite_h0 still applies of_injective to this map; finite_h0_h1 and degreeZero_scalar retain exact statements and structural coefficient action. No downstream finiteness hypothesis added.
7. Exceptions: all arbitrary original c/L and every class, same scalar zero/nonzero cases. No cancellation or positivity condition.
8. Own current evidence: positive81 run43658730606 at a2576203 passed74 full modules, including WholeChartRestrictionInjective10.085s and OriginalLineSectionsFinite4.174s, then CohomologyFinite failed22.121s. Error is missing Module Q on raw additive-sheaf terminal evaluation; subsequent degreeZero injectivity mismatch follows failed definition. Authentic own intake/result/log and unchanged definitions are pinned.
9. Verification: native Mathlib LinearMap/Rat and SheafCohomology/Basic fetched from exact56a005855ea17e0b0958f73ec801ae140b0a1679. Only two proof bodies change; no imported scope/options/trust/public theorem type changes. Native carrier definitional equality and instance elaboration remain hosted-unverified. Independent arithmetic source review precedes propagation; this is not a claim to close the module or lane.
