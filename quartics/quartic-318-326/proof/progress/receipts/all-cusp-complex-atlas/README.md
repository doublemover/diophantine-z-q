# Actual compact connected all-cusp complex curve

Strict Lean 4.35 replay and exhaustive recursive axiom audit: PASS, 73 declarations in eight producer modules. Only propext, Classical.choice and Quot.sound occur.

This packet constructs the genuine complex analytic atlas on the actual simultaneous all-cusp compactification. It builds on the separately frozen and audited `all-cusp-compactification` packet; the topology is its genuine TopCat gluing topology, not a substituted abstract compact space.

For the actual Gamma1(N) quotient with N >= 5:

- `WidthLocalInverse318` constructs an analytic local inverse for the actual width-w exponential, using its proved nonzero derivative.
- `RotatedPartialChart318` packages every actual rotated width-q homeomorphism as a genuine open partial chart, with exact source and punctured-disc target.
- `RotatedBiholomorphic318` proves both directions holomorphic in the existing genuine quotient complex atlas. The forward proof uses actual holomorphic local inverse sheets of the quotient covering. The inverse proof uses the actual width-exponential local inverse followed by the integral modular action and quotient projection.
- `AllCuspCharts318` registers a genuine complex ChartedSpace on the compactified source using all original quotient charts and every filled cusp disc.
- `AllCuspTransitions318` proves the exact old/new transition source and function, its analytic compatibility, and emptiness of the transition locus between distinct cusp charts.
- `AllCuspComplexCurve318.actual_compact_complex_curve` proves that this registered atlas is a complex analytic manifold, compact, Hausdorff, and second countable.
- `AllCuspEmbeddings318` proves that the original quotient embedding and every actual filled-disc embedding are holomorphic in the constructed structures.
- `AllCuspConnected318.compact_connected_complex_curve` additionally proves connectedness from the dense original quotient.

## Exact limits

The actual compact connected all-cusp analytic source is constructed here. Its cusp labels are the proved finite distinct high-neighborhood classes. An explicit equivalence with a separately packaged rational-cusp quotient, and numerical cusp/genus formulas, are not asserted. The particular algebraic modular cover and its analytic/algebraic comparison, the arithmetic/PEL source, and the global Arakelov comparison remain separate obligations. The previous packet's global genuine j extension is continuous with exact local G(q^w)/q^w expression. This packet does not by itself register a complex projective atlas on its OnePoint C target or assert the algebraic j-map comparison.

Run `bash build-all.sh`. This rebuilds all eight producer modules and an exhaustive import-all recursive axiom audit with `debug.skipKernelTC=false`. The audit includes public, private, and generated declarations and rejects every axiom except propext, Classical.choice, and Quot.sound.
