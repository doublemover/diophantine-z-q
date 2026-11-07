# Actual holomorphic fine-level quotient atlas

Strict-kernel PASS: 19 declarations in 5 modules, including 13 public theorems. All accepted modules were freshly rebuilt with `debug.skipKernelTC=false`, followed by exhaustive recursive axiom collection. Only propext, Classical.choice and Quot.sound occur.

## Constructed source object

The underlying space is the exact actual orbit base `PeterssonQuotient318.Base (GammaOneFiber318.image N)` for the genuine Gamma1(N) positive-matrix action, with N>=5. The frozen upstream packet already proves proper discontinuity, freeness, Hausdorff topology and an actual quotient covering/local homeomorphism. This packet constructs the complex analytic structure and proves the projection and its local inverse sheets are holomorphic.

## Proof chain

1. `LocalDeck318.locally_deck_eq` compares two actual continuous lifts with equal quotient projection. Choose the group element relating their values at the center. A genuine injective sheet of the proved covering, together with continuity of both lifts and of the action, forces that same element to relate them on a neighborhood. Local constancy is proved, not assumed.
2. `InverseCoordinate318.analytic_local_inverse` applies this to an actual local inverse of the quotient map. Its coordinate function agrees near every relevant point with one genuine positive-determinant Möbius transformation. Mathlib's actual complex analyticity of that transformation gives analyticity of the coordinate function. No inverse-regularity or transition hypothesis is supplied.
3. `HolomorphicCharts318.localChart` consists of the actual covering local inverse followed by the standard upper-half-plane complex coordinate. All transitions between these actual charts are proved analytic on their open source. `complexChartedSpace` is a concrete Mathlib atlas containing all these charts, with a chart at every point selected from actual quotient surjectivity.
4. `HolomorphicCharts318.complex_manifold` proves `IsManifold (modelWithCornersSelf complex complex) omega` for that exact structure. The proof supplies both directions of chart regularity through the analytic transition theorem and the actual open-domain uniqueness of derivatives.
5. `HolomorphicProjection318.quotient_holomorphic` proves actual analytic ContMDiff of the quotient projection. `HolomorphicInverse318.inverse_holomorphic` and `localInverseAt_holomorphic` prove analytic ContMDiffOn of each genuine inverse sheet on its actual source. Thus the covering is locally biholomorphic, not merely topological.

The atlas and manifold structure are explicitly named to avoid silently changing unrelated global instances; consumers install the named structure locally. The older frozen topological atlas is left unchanged. Both are structures on the same actual orbit quotient.

## Remaining boundary

This is the noncompact fine-level complex analytic quotient, not its compactification. Cusp charts/compactification, source PEL or modular-family interpretation, coarse quotients with possible stabilizers, arithmetic/algebraic models and their comparison with this analytic quotient remain separate. N>=5 and the exact Gamma1 subgroup are retained. No assertion of freeness for an arbitrary intermediate or diamond quotient is made.

A global differential line bundle and its identification with the already constructed orbit-fiber/Petersson norm are also separate; this packet proves the base's actual analytic atlas and quotient covering.

## Replay

Run `bash gamma-one-holomorphic-atlas/build-all.sh` from the parent directory. Frozen source hashes and dependency receipts are in `receipt.json` and `SHA256SUMS`. Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 are unchanged. No repository/Git changes were made. Exploratory check files and generated binaries are excluded from the accepted artifact.
