# Actual metric smoothness inference repair: nine obligations

1. Required inputs: same actual ComplexVectors, complex tau and strict upper-half-plane h_tau; original Riemann form, its constructed continuous real bilinear map and actual polarization metric. No smoothness conclusion or new geometric input is assumed.
2. Constructed objects: name the existing identity, constant complex I, I scalar-action map and diagonal pair map as explicitly typed ContDiff over R before the same composition. All are proved with native contDiff_id/contDiff_const/ContDiff.smul/prodMk.
3. Domain: every vector in the full original C^2 carrier, not a lattice sample, subspace or selected chart. All local metric fiber values remain unrestricted complex numbers.
4. Maps: exact z↦(z,I•z) into the original bilinear Riemann form; no alternative scalar action, real structure or transported topology. Composition and Gaussian weight consumer are unchanged.
5. Scalars: differentiation field R, constant scalar I in C, original complex-vector action and original exponent -pi*E(z,I z) retained. No sign, factor or metric normalization change.
6. Exceptions: h_tau>0 remains exactly as before; no nonzero-vector hypothesis or deleted origin. Smooth norm-square and whole local metric statements unchanged.
7. Consumer: smooth_weight feeds the identical squaredNorm product and smooth_local_metric. Existing secondLinear/bilinear definitions, smooth_form proof and all other code unchanged.
8. Own verification: torsion32 run43670426442 at7cbf02dd9bed3447c5d46502ebeb4f4c7aa7221b; own RESULT equals predecessor intake. LevelThetaFourier10.586s and Independence1.567s genuinely passed; MetricSmoothCoefficient fails10.735s solely at26:4 isDefEq deterministic200000heartbeat limit. Typed staging proposes inference reduction, not an observed performance result.
9. Honesty: proof-only source repair, no public telescope/import/option/resource/trust change, no local Lean/Lake or accepted module/packet claim. Independent exact source review and future own hosted replay required. No research source imported.
