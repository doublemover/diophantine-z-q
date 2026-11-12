# Bounded Jacobian audit repairs

Fresh candidate repairs against the supplied Windows audit at 038abb87429d1409a0208c13874e305f57f0ce1f. Each audited source is byte-identical to the corresponding source at reconstruction head 8ab60c2d6b654bec2fec07619c2e0ec9ef26c90d. Before/after copies preserve frozen packets. No local Lean was run and no kernel acceptance is claimed.

## Complete candidate repairs pending independent review

1. OriginalOpenLineRestrictionUnit318: close the actual naturality RHS grouping at line 79 with one right parenthesis. No declaration, map, bound, or proof step changes.
2. OriginalCartesianChartCoefficients318: supply the native implicit phi argument to IsIntegralHom.SpecMap_iff; replace hidden-map local Algebra instances by exact named instance_reducible definitions and explicit type/proof letI telescopes; parenthesize local notation B before field notation. polynomialAlgebra is the same composed actual map, expanded from OriginalSchemeDeckFieldAction318.baseAlgebra. It is not a new coefficient choice. All coefficient/tower/integral conclusions and actual Cartesian square hypotheses remain.

## Complete thickened-open candidate after full diagnostic

OriginalThickenedOpenSections318: normalize appTop explicitly before appLE composition and epsilon naturality. The full first goal is equality of two structure-presheaf maps induced by parallel arrows in the opposite open-set category. After the old simplification, congrArg and Subsingleton.elim prove equality of those arrows. All four logged failure sites now have source-level repair candidates; independent review and hosted Lean remain required.

## Actual consumers and next boundary

OriginalCartesianNormalChart318 consumes coefficient_tower and coefficient_integral with the same p, j, f, H and defines the same generic/chart/coefficient actions. It also contains independently unsafe hidden-map local instances. These are not part of the three recorded failure repairs and are not silently changed here. The current producer repair does not claim the downstream packet will finish.

## Evidence

AUDIT-DIAGNOSTICS.json retains the initially supplied compact records; full-logs now contains the three complete diagnostic logs from the subsequently supplied verified archive. primary/Integral.lean is freshly fetched at pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; SpecMap_iff binds implicit phi. Scheme.lean and OpenImmersion.lean are existing pinned project primary copies and expose appTop, app_eq_appLE, appLE_comp_appLE, map_appLE, appIso_hom'. All local write actions were authorized OpenAI-cloud writes; no user-computer access.
