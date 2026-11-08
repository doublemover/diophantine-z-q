# Actual complex-fiber algebra and scheme comparison

This packet strengthens the canonical rank-four complex-point comparison to an explicit algebra isomorphism after actual scalar extension.

- Over any commutative coefficient ring with 3 invertible, construct inverse algebra maps between the normalized third-division quartic algebras under A ↦ s²A, B ↦ s³B for an actual unit s. The maps send the coordinate generators to s*x and s⁻¹*x. The proof works with nilpotents and does not infer an algebra isomorphism from a point count.
- Transport the literal integral quartic algebra along its actual evaluation at genuine analytic j, using the proved monogenic base-change equivalence and the exact mapped polynomial.
- Apply the canonical, sign-independent x-scale to obtain an actual ℂ-algebra isomorphism from the literal arithmetic x-algebra's scalar extension to the genuine analytic elliptic curve's third-division algebra.
- Use the previously proved full-diamond fixed-algebra identification to obtain the same isomorphism for the actual fixed arithmetic algebra. Prove the exact coordinate-generator formula.
- Apply Spec to obtain an actual isomorphism of the corresponding complex affine schemes.

This is a precise comparison of the complex algebraic fibers of the specified arithmetic family. It does not identify a global arithmetic modular curve with an upper-half-plane quotient, prove a global scheme analytification theorem, construct general-level arithmetic models, treat j=0 or j=1728, or establish a PEL comparison. N is the base-localization level; the torsion order is three.

Verification uses Lean 4.35.0, debug.skipKernelTC=false, sequential module replay and recursive import-all auditing of every declaration, including private/generated declarations. Only propext, Classical.choice and Quot.sound are permitted. This is an author replay against pinned predecessor/Mathlib caches, not independent review or full dependency-closure replay. Run build-all.sh only while holding the workspace compile lock.
