# Fresh reconstruction: full normal-order Hom localization

## 1. Whole module localization

Required: The map from the entire old integral closure N to the Q-integral closure O must localize at powers of the BASE coordinate, not merely its raw-order generators.

Constructed and justification: IntegralClosureModuleLocalization318.localization uses actual inclusion and both explicit algebra towers, native isLocalizedModule_iff_isLocalization, and the previously constructed full Away localization.

Sources: IntegralClosureModuleLocalization318.lean; IntegralClosurePrincipalLocalization318.lean; LocalizedModuleIsLocalization.lean

## 2. Actual finite presentation

Required: Full Hom localization requires finite presentation of N over P.

Constructed and justification: NormalOverlapFinitePresentation318 produces finite normal order via surviving LocalizedNormalModel finite_normal_model; Noetherian P then gives finite presentation. Reciprocal finiteness uses the independently constructed old reciprocal normal closure. hd is retained explicitly.

Sources: NormalOverlapFinitePresentation318.lean; LocalizedNormalModel318.lean; IntegralInfinityNormalConductor318.lean; ModuleFinitePresentation.lean

## 3. Every functional

Required: The localized Hom must contain all P-linear functionals O to Q, not only an image or named frame.

Constructed and justification: Native isLocalizedModule_map applied to actual inclusion and Algebra.linearMap P Q proves full-Hom localization; native IsBaseChange equiv gives Q tensor Hom(N,P) equivalent to Hom_P(O,Q).

Sources: IntegralClosureFullDualLocalization318.lean; ModuleFinitePresentation.lean; LocalizationBaseChange.lean; IsTensorProduct.lean

## 4. Literal evaluation

Required: The Hom equivalence must extend the OLD functional, not an arbitrary equivalence of modules.

Constructed and justification: map_value is native IsLocalizedModule.map_apply. one_value explicitly normalizes IsBaseChange.equiv on one tensor and evaluates on the literal inclusion of EVERY n.

Sources: IntegralClosureFullDualLocalization318.lean; LocalizedModuleBasic.lean; IsTensorProduct.lean

## 5. Finite application

Required: All generic scalar towers must be supplied at the actual finite normal order.

Constructed and justification: Uses finiteMap and exact finite_polynomial square, same N and FiniteOverlap, with actual finite_presentation producer. No flatness or freeness premise is inserted.

Sources: IntegralNormalOverlapFiniteDual318.lean; IntegralOriginalNormalOverlap318.lean; OriginalNormalOverlapOrderLocalization318.lean

## 6. Independent reciprocal application

Required: Reciprocal polynomial and Laurent actions must not silently be replaced by finite scalars.

Constructed and justification: Installs old sourceAlgebra/baseAlgebra/tower, exact infinityMap and infinity_polynomial square; consumes infinity_presentation. Both native maps retain literal inverse-coordinate interpretation.

Sources: IntegralNormalOverlapInfinityDual318.lean; IntegralInfinityReciprocalScalar318.lean; IntegralOriginalNormalOverlap318.lean

## 7. Old trace object

Required: The localized functional must consume the same existing trace-codifferent coefficient.

Constructed and justification: trace_coefficient supplies the old exact polynomial p and separately its image in the Laurent base and old open base F. The latter remains Algebra.trace F B(z*n). No unproved equality of ambient coefficient paths is used.

Sources: IntegralNormalOverlapFiniteDual318.lean; IntegralNormalOverlapInfinityDual318.lean; IntegralNormalizationTraceFunctional318.lean; IntegralInfinityTraceFunctional318.lean

## 8. Separation and exact point

Required: All integral inputs must separate whole localized Hom, and original per-place data must be retained.

Constructed and justification: Native linearMap_ext proves ext/eq_iff from every n, with s explicitly included. Multiplication precomposition is evaluated exactly. OriginalNormalOverlapFullHom318 supplies both equivalences at original c,t,w,D using the actual source-domain producer and coefficient nonzero facts.

Sources: IntegralClosureDualRestrictionSeparation318.lean; OriginalAllPlaceNormalizedData318.lean; IntegralDistinctContactOpen318.lean; OriginalNormalOrderFiniteDual318.lean

## 9. Boundary and inherited corrections

Required: Do not transfer lost acceptance, known audit failures, or jump to sheaf/Hodge claims.

Constructed and justification: Six fresh modules rebuild Hom only. Five inherited sources use exact independently reviewed audit candidates, with explicit before/after deltas; 1505 predecessor sources are exact. No O-linear sheaf gluing, reciprocal-Hom equivalence, negative-t-squared differential factor or global dualizing/Hodge/regularity assertion is made.

Sources: INHERITANCE.json; HOM-REBUILD-PRIMARY/geometry-audit-repair-source-review.json; HOM-REBUILD-PRIMARY/pel-audit-three-repairs-review.json
