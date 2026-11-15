# Cofactor r6 exact hosted rewrite-boundary repair

SOURCE-ONLY CANDIDATE; inactive; no local Lean or kernel acceptance.

Own run43723785714 at964435f03d8c11dbb6b52b8453fa0c4140a445d9 passes12 complete draft modules then fails NormalizedCofactorFirstOrder318 in4.326s, leaving4 roots unreached. The error is not a resource failure: projection generator rewrite at96 sees f.toRingHom rather than the f application in hr; two native differential rewrites at117/128 see a projection witness typed with f rather than the explicit fieldPoint identity composite. Earlier binder/evaluation-algebra errors no longer appear, but no declaration from the failed module is accepted separately.

The first change makes both sides of the generator change explicit with the same AlgHom f. The second constructs projection_fieldPoint from the SAME existing projection theorem, with the exact visible native fieldPoint V A V f result type, and supplies that typed witness to integralFiberMap. Existing rw steps now receive the literal expected witness type, without changing the ring/algebra operations, mathematical hypotheses or chosen point. This is a source-supported repair hypothesis, not a hosted success claim.

All original declarations keep their types; one new helper theorem exposes the existing definitional identity composite. Actual source parameters V,d,a,T,z,hz,f,hf,hr and the full cotangent fiber remain. All signs, arbitrary integral/nonunit/zero roots and residue characteristics remain admitted. The Jacobian product M, signed cofactors, determinant, root relation, full first-order lift and differential outputs are unchanged. No unit premise, root inversion, generic-fiber restriction, option increase, axiom, sorry or kernel bypass.

The compact next packet remains17 roots with19 baseline dependencies (36-source closure); no original-normalization research modules enter it. The new quotient candidate remains independent, inactive and dependency-blocked. No intrinsic dualizing, regular/maximal-model, infinity/proper-gluing, all-place or GeometricRealization claim.
