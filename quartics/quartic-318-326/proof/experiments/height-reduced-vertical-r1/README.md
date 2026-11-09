# Reduced vertical fibers give the original uniformizer

Draft only. No local Lean execution. Hosted strict compilation and independent acceptance are pending. The two integral-tensor predecessor modules are copied unchanged from `height-integral-tensor-r1`.

`ReducedVerticalUniformizer318.irreducible_of_reduced_quotient` proves: in an actual DVR B, a nonzero nonunit x for which B/(x) is reduced is irreducible. It decomposes x into a unit times a power of a DVR generator. The generator's image in the reduced quotient is nilpotent, hence zero; this identifies the actual maximal ideal with (x), so the original x is a uniformizer. Irreducibility is a conclusion, not a supplied ramification assertion.

`ReducedVerticalTensorSections318.integral_sections` consumes this result for the actual rational parameter p and the existing constructed fraction derivation/tensor lattice. It produces actual integral tensor preimages of the literal J²-scaled quadratic differentials. No unit-2, distinct-reduction or contact-avoidance hypothesis is used in this local vertical implication; it applies at contact-collision primes whenever its actual reduced-fiber hypotheses hold.

## Essential scope and normalization boundary

This does not construct a semistable model, prove a particular special fiber reduced, or identify an integral cotangent frame of such a model. Those geometric inputs remain explicit.

In particular, reducedness of B/(p) is not inferred from semistability after an arbitrary ramified extension of the base number field. In that case the reduced special fiber is defined by the base's uniformizer pi, which need not be the rational prime p. The generic x theorem applies to such a parameter, but this packet's section consumer still uses p. A subsequent killed-base-uniformizer version is needed before applying the section theorem in that setting. No ramification factor is dropped.

The source paragraph read is `docs/sources/quartic_v10.tex` lines 7029–7037. Existing scalar derivative/section sources and the actual upstream DVR/nilpotent sources at pinned Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679 were read. Their hashes and source URLs are recorded. The manuscript and accepted progress snapshot are unchanged.

## Application contract

1. Objects. B is the actual local DVR and B/(x) is its actual principal-ideal quotient. The tensor consumer uses the same B and its actual fraction field K with the original relative base R.
2. Quantifiers. The reduced-quotient theorem applies to every nonzero nonunit x, not just a chosen generator. The section consumer quantifies over both original tensors, every t, and every p satisfying its actual reducedness hypotheses.
3. Domain. Reducedness is assumed for the precise quotient by x or p. It is not inferred for a rational prime from reducedness modulo a ramified base uniformizer. No missing vertical point is silently declared covered.
4. Maps. The proof uses the actual quotient map, its kernel membership theorem, and the maximal ideal in the original DVR. The consumer uses the previously verified integral-to-generic cotangent tensor map, preserving its direction and coefficient normalization.
5. Scalars. The original parameter x is proved irreducible via ideal equality, with no valuation renormalization. The source J², contact polynomial and second-section factor t are unchanged. Ramified base factors remain an explicit boundary.
6. Consumer. The derived irreducibility of p is fed into VerticalCotangentSections318.integral_sections, whose coefficients are exactly the source scalar sections. The conclusion consists of actual tensor preimages, not supplied valuation or integrality estimates.
7. Hypotheses. The DVR decomposition requires x nonzero. Reducedness kills the generator's nilpotent quotient image. Nonunit x gives the reverse maximal-ideal inclusion. The source tensor theorem still requires an actual integral Kahler frame and the actual fraction field; neither is asserted to exist geometrically here.
8. History. The classical source uses reduced vertical geometry to justify its uniformizer statement. Existing Lean modules already prove the derivative and coefficient implications from a uniformizer. This packet supplies the local reduced-quotient implication and preserves the ramified-base limitation, rather than claiming complete geometric realization.
9. Verification. Copied sources, source imports, consumer sources and exact upstream versions are hash-bound. Static checks are structural only. Hosted strict checking, recursive private-inclusive audit and distinct acceptance remain pending; no independent approval is fabricated.
