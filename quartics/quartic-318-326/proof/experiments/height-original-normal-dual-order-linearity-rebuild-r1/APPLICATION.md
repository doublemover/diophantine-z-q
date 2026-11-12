# Fresh normal-order linearity reconstruction

## 1. source_hypotheses

Required: Full Hom localization requires finite presentation over the polynomial base and the actual principal localization of N.

Construction and justification: Uses the accepted full Hom producer and actual integral closure Away localization. Finite presentation is constructed separately on finite and reciprocal charts, not assumed free.

Sources: IntegralClosureDualOrderBaseChange318.lean

## 2. constructed_objects

Required: O must act on Hom by multiplication on its input, not by values in Q.

Construction and justification: ValuedDualPrecomposition318 constructs the action explicitly on the entire Hom; its baseTower compares to pointwise P action using actual functional linearity. Old finite-dual identification has literal identity functions and exact action.

Sources: ValuedDualPrecomposition318.lean

## 3. index_domain_coverage

Required: Order-linearity must hold for every old n and every functional, not only root generators.

Construction and justification: map_action proves equality using full localization separation on all old m. Products use the actual inclusion ring map; no finite-basis shortcut.

Sources: IntegralClosureDualOrderLinearity318.lean

## 4. transition_maps

Required: The new N-linear map must be exactly the old P-linear localization map.

Construction and justification: restrictScalars proves literal equality. Source, target P/N and N/O towers are constructed explicitly with precomposition actions.

Sources: IntegralClosureDualOrderLinearity318.lean

## 5. limiting_object_identity

Required: The native tensor equivalence must target all Hom_P(O,Q).

Construction and justification: Native IsLocalizedModule.of_restrictScalars upgrades the old full localization, then the SAME O is a localization of N. Native isBaseChange.equiv gives O tensor_N Hom_P(N,P) equivalent to the complete valued Hom.

Sources: IntegralClosureDualOrderBaseChange318.lean

## 6. coefficient_conventions

Required: One-tensors and integral coefficient tensors must retain literal old evaluation.

Construction and justification: one_value and integral_tensor_value normalize native equiv_tmul and actual multiplication. They return algebraMap P Q(f(a*n)); no trace denominator or differential factor is silently inserted.

Sources: IntegralClosureDualOrderBaseChange318.lean

## 7. local_conditions

Required: Actual finite and reciprocal charts have independently defined polynomial/Laurent actions.

Construction and justification: Both application modules install their original scalar structures and exact polynomial squares. The reciprocal ring-map equality is evaluated by RingHom.congr_fun; finite square is already pointwise.

Sources: IntegralNormalFiniteDualOrder318.lean; IntegralNormalInfinityDualOrder318.lean

## 8. exceptional_cases

Required: The per-place model must keep the exact original coefficients and nonzero hypotheses.

Construction and justification: OriginalNormalDualOrderLocalization318 uses original c,t,w,D, constructs source domain from contacts injective and coefficients nonzero, and retains both independent normal-order actions. No bad-prime exclusion or regularity assumption.

Sources: OriginalNormalDualOrderLocalization318.lean

## 9. downstream_consumption

Required: Do not promote a full O-linear module comparison to native sheaf gluing or Hodge identification.

Construction and justification: This packet supplies the concrete module producer needed for later tilde restriction. It does not yet prove native sheaf base change, finite-versus-reciprocal dual equality, full intersection or global dualizing/Hodge comparison. All1516 inherited sources are exact, including reviewed audit replacements.

Sources: README.md; INHERITANCE.json
