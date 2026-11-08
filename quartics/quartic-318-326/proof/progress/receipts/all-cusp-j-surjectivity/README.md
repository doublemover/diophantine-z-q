# Genuine analytic j-surjectivity and actual arithmetic source surjectivity

This packet joins the already-constructed all-cusp compactification with the complex open-mapping theorem and the actual period/arithmetic comparison.

- Prove that the genuine analytic j-image is open: the actual function is holomorphic, and the previously proved cusp asymptotic rules out constancy.
- Prove that this image is closed in the complex plane: it is precisely the finite part of the continuous j-image of the actual compact all-cusp curve. Every attached point is a genuine cusp and maps to infinity.
- Connectedness of the complex plane then proves that every complex number is a value of genuine analytic j. Compactness is the previously proved finite fundamental-domain/closed-disc construction, not an assumed properness premise.
- Combine this with actual integral modular-orbit surjectivity on the three-torsion fibers to prove that the constructed map from the existing admissible Gamma1(3) quotient is onto every complex point of the specified literal full fixed arithmetic algebra.
- Use the full faithfulness of Spec to state surjectivity onto every actual Spec(C)-valued point of that arithmetic affine scheme.

This is a genuine global surjectivity theorem, not a global modular-curve isomorphism. Injectivity of the source map, its holomorphic variation, the analytic/arithmetic comparison through elliptic values and cusps, and a PEL identification remain unproved. N parameterizes the arithmetic base localization; the torsion order is three.

Verification: Lean 4.35.0 sequential replay with debug.skipKernelTC=false and exhaustive recursive import-all axiom auditing, including private/generated declarations. Only propext, Classical.choice and Quot.sound are allowed. This is author replay against pinned predecessor/Mathlib caches, not independent review or a full dependency-closure rebuild. The exact uncached Mathlib.Analysis.Complex.OpenMapping target was built from the pinned Mathlib source. Hold the workspace exclusive compile lock for build-all.sh.
