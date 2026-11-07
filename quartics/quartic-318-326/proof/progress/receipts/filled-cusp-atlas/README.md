# Actual complex atlas on the single-cusp filling

Strict Lean 4.35 replay and exhaustive recursive axiom audit: PASS, 23 declarations in four producer modules. Only propext, Classical.choice and Quot.sound occur.

The underlying space is the actual TopCat gluing from `single-cusp-gluing`, with Hausdorffness and second countability established in `cusp-hausdorff` using the genuine j-growth. For N >= 5:

- `FilledCuspCharts318` constructs old quotient charts and the actual filled-disc chart, proves their centers/sources/values, and registers a genuine complex ChartedSpace.
- `FilledCuspTransitions318` identifies the old/new transition, including its exact source, with the already proved biholomorphic cusp transition on the original quotient. It proves actual complex-analytic compatibility.
- `FilledComplexCurve318.filled_isManifold` proves the actual registered atlas is a complex analytic manifold. `filled_complex_curve` packages it with Hausdorffness and second countability.
- `FilledCuspEmbeddings318` proves the actual original-quotient and filled-disc embeddings holomorphic in these registered structures.

Exactly one infinity cusp is filled. This does not assert that all cusps have been attached or that this space is compact/proper. Identification with the particular algebraic modular cover, arithmetic model, PEL interpretation and global Arakelov source remain separate.

Run `bash build-all.sh` from this directory. The script uses the installed project toolchain and frozen dependency packets. `FilledCuspAtlasAudit318.lean` imports all declarations, including private/generated ones, and checks their complete axiom dependencies.
