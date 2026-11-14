# original-five-kernel-norm-equivalence-r21

Draft successor to `original-five-kernel-norm-equivalence-r20` at `57227e167abe49436d651b932ff75d5bdf9b5898`.

## Exact hosted evidence

Run 43603177874, job 132472792456, artifact 14117462707. OriginalDualAlgebraNormTrace318 passed4.429s, followed by OriginalFiniteFreeDualTransfer3182.371s, FifthActualLocalDualNorm3182.020s, CharacterActualPrincipalBasis3182.121s and CharacterActualLocalDualNorm3182.021s. DualUnitFactorization318 then failed2.823s: reduction of the actual infinitesimal unit remained an unapplied fst ring-hom projection, and normalized.map_mul left a commutative-unit reassociation goal.

## Bounded repair

In coefficient_unit expose the exact (1 + inr a).fst goal and simplify. In normalized.map_mul use only the two native monoid-map laws and inverse-product law, then AC normalization. Actual coefficient/lift/normalized/log definitions, all arbitrary-unit claims, original maps and downstream arguments remain unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Source-only repair of two exact hosted goals. No local Lean or successor acceptance. Native carrier normalization and later unit/norm consumers still require hosted checking; no domain, hypothesis, scalar action, module boundary or resource limit is changed.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
