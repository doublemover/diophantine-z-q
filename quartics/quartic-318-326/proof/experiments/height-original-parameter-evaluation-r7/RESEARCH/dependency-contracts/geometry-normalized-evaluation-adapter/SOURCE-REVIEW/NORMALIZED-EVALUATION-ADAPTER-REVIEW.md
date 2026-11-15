# Independent same-center cotangent evaluation adapter review

Verdict: PASS for the exact two-source construction and current standalone research contract. This is source-only review, not Lean compilation, an active packet, accepted proof dependency, compiled axiom audit or a global geometric realization.

Reviewed APPLICATION `609c20fdb43281bafedd2e0d4d61bd7d8bf803089bd9644e6159fb3bf9c54f6d`:
- NormalizedPointEvaluationInput318 `d3dfcb4247e72bfb0a39d61c1cf5add1fae47d3a46ad6e8dacd48049f5917d47`.
- NormalizedAllPlaceEvaluations318 `ad1c2f1137bdce6a75c27a6aafc6ff9d98de2d60e17d8dc06199fcd5b711a4f4`.

## Exact construction and proof applicability

The field_polynomial helper starts with the same V-algebra point f:A→V, its entire polynomial evaluation identity, and the same coordinate equality algebraMap(T)=t. The exposed fieldPoint is precisely A→V→K. The proof changes only to this composite and rewrites the integral evaluation through pinned Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, in its actual reverse direction, then hT. I checked the complete native declaration and base64 API bytes/Git blob d053dc25e14cfbce5f59b5fedef991473f30951a at the fixed Mathlib commit. No second field identity, alternative point or unsupported polynomial scalar action is supplied.

Finite root nonvanishing uses the exact signed equation s_i*fieldPoint(root_i)=y_i and y_i≠0. Reciprocal nonvanishing uses s_i*t*fieldPoint(root_i)=y_i. Setting the root value to zero contradicts y_i≠0 without cancellation of s_i or t, and without declaring either an integral unit. The reciprocal t factor is retained rather than silently replaced by the finite formula.

Each evaluation theorem instantiates the already source-reviewed finiteEvaluation/infinityEvaluation and its dX theorem with precisely this f, the derived field-polynomial identity and the derived nonzero generator values. The result type retains the explicit fixed-f local Algebra A V := f.toRingHom.toAlgebra. The dependent functional is the original V-linear map from V tensor_A Omega(A/V) to K; no hidden-f instance registration, alternative tensor base or arbitrary functional is introduced. The exact dependency types use the same local action, and their selected function and normalization theorem have matching f/hf/hn arguments. Elaborator verification remains outstanding.

The final adapter derives y_i≠0 for every Fin4 label from y_i²=c_i*(t−a_i), the supplied c_i:K units and the explicit t≠a_i condition. It calls chart_center_alg once. Its existential u/e/s, nonzero s, coefficient normalization, finite or reciprocal original point f, all-polynomial identity and all four signed root equations are preserved in the result, and the new functional is appended within that same branch. The proof eliminates existential/disjunctive witnesses into a proposition, not into data by illicit Prop elimination. No new center, sign, parity label or pole is selected.

## Nine current research obligations

1. **Original inputs.** V remains a DVR with domain structure, K its characteristic-zero fraction field, pi a supplied irreducible, c four K-units, and the original square equations. The additional nonzero-radicand condition is explicit. This is pointwise in these data, not construction of a coherent global model or all-place family from nothing.
2. **Objects.** Both entire normalized four-root orders and their genuine integral cotangent pullbacks are used. There is no replacement by field differentials, a different quotient, an abstract line or a chosen metric.
3. **Domain.** All four generators and all polynomials are retained. Residue characteristic two, nonunit twists and the finite/reciprocal alternatives are allowed. Root-zero/branch points are excluded by ht from this first-order division route, not proved covered. The older all-point center theorem is unchanged.
4. **Maps.** The literal f and A→V→K are retained. No extra field-point or scalar-compatibility premise appears; it is derived from the same polynomial input. The fixed local algebra action agrees with the reviewed dependency API.
5. **Scalars and normalization.** Original u_i*pi^(e_i), s_i², finite s_i and reciprocal s_i*t formulas remain. Finite DX=1 means DT=1; reciprocal DX=1 means Dw=1 for w=1/t, not Dt=1. The rational-frame differential rescaling is not discharged.
6. **Consumer.** ev(DX)=1 supplies a nonzero image element for the separate finite-image/FG/frame route. There is no new direct consumer imported from that pending geometric chain. The present result does not supply the original quadratic-section lifts or identify their evaluations.
7. **Exceptional cases.** Division by two and root values occurs only in the reviewed field-valued first-order dependency, with characteristic zero and nonzero roots; no inverse of two is asserted in V. Singular orders, torsion cotangent modules, and nonunit twists are not removed by a regularity hypothesis. A field-valued functional may have bad-place denominators.
8. **Residual geometry.** Neither maximal-model dualizing/bicanonical lattices, native Hodge/KS image, metric compatibility, support bounds nor height estimates are constructed. The cotangent-image lattice is not equated to a maximal-model lattice. No GeometricRealization conclusion follows from this adapter alone.
9. **Verification.** All 1,877 owner bindings and every obligation reference resolve. The exact six current dependency sources match their separately reviewed source bytes and bound review reports. The prior APP 1471e655 and its dependency snapshot are retained, while the active point dependency is the corrected reviewed be6427f2. The README's earlier pending descriptions are explicitly retained as history by its final update; they are not current acceptance claims. All sources remain uncompiled here.

## Provenance and inactive plan

Both adapter source files are byte-identical to their pre-dependency-update versions. I checked the historical 96 center-r68 root hashes directly against Git at 57227e167abe49436d651b932ff75d5bdf9b5898 and verified the 104 distinct-root inactive order including the six reviewed prerequisite files and these two files, with internal imports ordered before use. This is a historical root plan, not a current hosted intake or assertion that every transitive dependency is newly admitted or reached. External imports are recorded separately. No production root, resource/trust setting, workflow, cache or acceptance flag is changed. A future experiment must have its own current closure/contract/integration review and actual hosted evidence.

The companion checker, exact source/dependency/primary snapshots and full owner-binding inventory substantiate these source/provenance findings. They do not replace Lean type checking or a compiled recursive axiom audit.
