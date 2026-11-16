# Actual level-theta Fourier namespace repair

Own torsion31 at eeb2a2fb55e45c09bde7e013bef8f98d2f00be51, run43667489535. No local Lean.

1. Inputs: arbitrary tau:Complex, retained strict upper-half-plane h_tau where required, arbitrary nonzero level N, every characteristic r:Label N, integer pair k and real representative x. No positivity/level assumption changed.
2. Objects: same scaled term, torusTerm and full continuous-map torusTheta Banach sum. Native Fourier evaluation theorem is global _root_.fourier_coe_apply, not in AddCircle namespace.
3. Domain: full actual real unit two-torus and all integer frequencies/characteristics, not a finite Fourier truncation or selected subseries.
4. Maps: exact realPoint, torusPoint, frequency and native mFourier. Correct namespace exposes the same two real-representative characters, allowing the existing exp_add and ring steps.
5. Scalars: exact inverse level1/N, original quadratic tau coefficient, positive2*pi*I linear exponent and unit-circle Haar probability normalization unchanged. No sign, N factor, characteristic filter or complex inner-product convention altered.
6. Consumer: same real_evaluation via ContinuousMap.evalCLM; same continuous Fourier functional on L2 and its orthonormality, frequency injectivity and full HasSum yield fourier_exact for every r,k.
7. Exceptional cases: both accepts and rejected-index branches retained; k=0 and all real coordinate zeros included. N=0 remains excluded only by existing NeZero N. No nonvanishing theta-at-origin assumption.
8. Own evidence: RESULT packet hash equals actual current intake. ThetaRealTorus now passes9.041s; LevelThetaFourier fails9.442s after54 successful commands. Exact failure is unknown AddCircle.fourier_coe_apply, then unexpanded characters block exp_add. Deprecation/linter warnings are not failures. No downstream or candidate completion claim.
9. Boundary: one identifier only. All definitions, statements, imports, options, instances, other proof bytes and full analytic hypotheses unchanged. Independent source and propagation checks precede hosted replay; no new trust/resource settings or Lean acceptance.
