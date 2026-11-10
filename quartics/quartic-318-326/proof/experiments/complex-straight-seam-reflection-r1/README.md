# Holomorphic gluing and Schwarz reflection across a real seam

Constructs rectangle-based Morera gluing for continuous functions holomorphic off the real axis, then constructs the actual Schwarz reflected holomorphic extension from closed upper-side data. This is an analytic prerequisite for the original maximal-quotient conformal route, not a substitute for its still-needed boundary extension.

## Application contract

1. **Objects:** Prove an analytic gluing theorem on actual complex open subsets. The source and target are complex numbers with their original complex derivative. No alternate complex structure is transported through a topological homeomorphism.

2. **Indices:** Cover every rectangle and every point on both sides of the real seam. IsConservativeOn is constructed for arbitrary rectangle endpoints, including reversed heights and seam edges. Ordered crossing rectangles split at imaginary height zero.

3. **Domain:** Retain all domain and continuity hypotheses visibly. The straight-seam gluing theorem takes an open U, continuous f on U, and actual complex differentiability off the real axis. The reflection theorem instead constructs this continuity from upper closed-side continuity and matching real boundary values.

4. **Coefficients:** Keep exact contour signs and original integrals. The rectangle integral uses both horizontal integrals and both vertical integrals with exact imaginary-unit factors. Adjacent vertical interval integrals are justified by continuity on the original rectangle, then cancel exactly.

5. **Local conditions:** Construct seam holomorphy rather than assume it. Cauchy-Goursat is applied only on rectangles with open interiors off the seam. Crossing rectangles split into two such rectangles. Pinned HasPrimitives Morera then supplies complex differentiability on the whole open set.

6. **Transition maps:** Construct reflected extension and its continuity. extension f uses f on the closed upper side and conjugate(f(conjugate z)) on the lower side. Conjugation invariance of U, real seam values and closed-side continuity imply continuous gluing through ContinuousOn.if.

7. **Identity:** Prove actual Schwarz reflection. Genuine conjugate-conjugate differentiation proves lower-side holomorphy. The new Morera gluing result proves the extension holomorphic at the seam. Exact upper agreement and full lower reflected formula are retained.

8. **Consumers:** Keep the remaining polygon conformal tasks separate. This is a generic straight-seam reflection producer needed for the actual original half-cut. It does not construct a Riemann map, Caratheodory boundary extension, circle flattening, maximal complex P1 or algebraization.

9. **Validation:** Use pinned mathlib and independent source/hosted verification. The two-source packet imports pinned HasPrimitives, CauchyIntegral and Deriv.Star. No extra axioms, sorry, local Lean build, external theorem assumption or budget increase is introduced. Source review is separate from kernel acceptance.
