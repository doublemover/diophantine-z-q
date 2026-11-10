# Constructed rectangle primitives and bounded closure extension

Builds the actual primitive of any holomorphic function on an open rectangle by wedge integration, and extends that primitive uniformly continuously to the closure when its derivative is bounded. Independent of the Riemann-mapping port. It does not yet glue the upper/lower boundary primitives or extend the derivative itself.

The wedge-integral/local-disk method uses the public pinned mathlib HasPrimitives theorem (authors Ian Jauslin, Alex Kontorovich, Oliver Nash); the rectangle path-independence and closure join are supplied here.

## Application contract

1. **Objects:** Construct primitives on actual complex open rectangles. The function is complex differentiable on Ioo(a,b)×Ioo(c,d). Its primitive is the actual two-segment wedge integral imported from pinned mathlib HasPrimitives, not a supplied primitive or formal symbol.

2. **Indices:** Cover all points and all intermediate horizontal/vertical segments. Every interval integral between coordinate endpoints inside the open rectangle is integrable by continuity and exact coordinate interval containment, regardless of endpoint orientation.

3. **Domain:** Prove global rectangle path independence. Cauchy-Goursat on the actual rectangle between mixed-coordinate corners and exact adjacent integral identities give wedge_difference at every triple of original points.

4. **Coefficients:** Keep the correct complex contour factors. Horizontal integrals and imaginary-unit times vertical integrals retain the original wedge definition. The global/local primitive join is an exact equality, not a path homotopy assumption.

5. **Local conditions:** Construct the derivative of the same global primitive. At every original point an actual contained disk supplies the pinned local wedge derivative. Global wedge_difference identifies the global primitive locally with that local primitive plus its original constant, yielding derivative f.

6. **Transition maps:** Construct boundary extension through genuine uniform completion. The original subtype embeds uniformly and densely in its closure. Uniformly continuous complex-valued functions extend through completeness of the complex target, with exact agreement on the original domain.

7. **Identity:** Derive bounded primitive extension without pre-assumed boundary values. For a bounded holomorphic f, the constructed primitive has bounded derivative. Convex mean value gives its Lipschitz bound, then the uniform extension produces continuous values on the whole closure.

8. **Consumers:** Separate primitive extension from holomorphic extension of f. No Riemann port, conformal boundary value, vanishing-jump hypothesis, compact P1 or algebraization is used. Matching upper/lower primitive traces and differentiating their glued extension remain subsequent analytic work.

9. **Validation:** Use pinned public analytic/topological APIs and independent review. The proof extends the pinned HasPrimitives wedge method to rectangles and uses pinned MeanValue and UniformEmbedding completion. No local Lean build, new axiom, assumed primitive or empirical limit is introduced.
