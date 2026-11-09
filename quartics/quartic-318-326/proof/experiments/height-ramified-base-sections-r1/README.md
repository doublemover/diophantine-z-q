# Vertical section tensors over a ramified arithmetic base

Draft only. No local Lean execution. Hosted strict compilation and independent source acceptance are pending. Four prerequisite modules are copied unchanged from `height-reduced-vertical-r1`.

The previous local consumer used the rational prime p as uniformizer. This packet removes that restriction without rescaling its valuation or dropping a ramification factor.

`KilledUniformizerSections318` proves the exact source coefficient integrality for an actual DVR uniformizer pi killed by the actual relative derivation. Its proof retains the original canonical valuation of B, all four original contacts, and J=2765952000. The four-factor and integer-difference estimates are the existing source lemmas; only the derivative step is generalized from a rational prime to the killed uniformizer. Both integral coefficients are produced from the actual DVR valuation.

`ReducedBaseTensorSections318` takes an actual base element r in R, requires its image in B to be nonzero and nonunit, and requires precisely B/(r) reduced. The reduced-quotient theorem derives irreducibility of that image. The fraction derivation constructed from the integral Kahler frame kills it because it is an actual relative base element. The resulting scalar integrality is converted to actual integral cotangent tensor preimages of J²(dt tensor dt)/P(t) and t times this tensor.

Thus the local implication can be used with a ramified base's actual uniformizer: it does not require reducedness modulo the underlying rational prime or assume that prime has valuation one. This is not yet a construction of the required semistable model, proof of reducedness for its actual fibers, construction of its integral frame, or verification of every required vertical place. All those geometric inputs remain explicit.

The totalized field-division boundary of the tensor predecessor is retained. Interpreting the displayed generic tensors as rational differential evaluations requires the contact denominator nonzero; the zero-denominator value is not used to infer horizontal branch regularity.

Actual source read: `docs/sources/quartic_v10.tex` lines 7029–7037, VerticalDerivation318, VerticalSection318 and FractionSourceSections318. The generalized proof follows the original valuation calculation and identifies the exact changed hypothesis. No existing source or acceptance record is edited.

## Application contract

1. Objects. The local ring is the actual DVR B, K its actual fraction field, and R its actual relative base. The reduced quotient is by algebraMap R B r, not by a substituted rational prime. The output is in the original cotangent tensor squares.
2. Quantifiers. Every original contact and both literal sections remain covered. The local estimate permits any killed uniformizer and any t, subject to the existing rational-differential interpretation boundary. No global family of places is declared covered by this local theorem alone.
3. Domain. Reducedness and nonzero/nonunit hypotheses are imposed on the precise base parameter image. They may apply to a ramified base uniformizer. Existence of a reduced-fiber model or a frame at an actual missing place is not inferred.
4. Maps. Base scalar R to B to K follows the original algebra tower. The constructed fraction derivation extends the integral frame derivation, so killing the base parameter is proved by the actual derivation coefficient law. Integral coefficients are converted through the actual tensor-map image criterion.
5. Scalars. Canonical valuation B to K is never renormalized. The original v(J), all integer contact differences, J², and second-section factor t are retained. There is no assertion v(p)=1 and no lost ramification index.
6. Consumer. ReducedBaseTensorSections318.integral_sections constructs tensor preimages of the exact VerticalCotangentSections318.q0/q1. It does not return a newly normalized pair or replace the original frame with arbitrary scalar norms.
7. Hypotheses. The generalized scalar theorem requires an actual killed uniformizer and integral-preserving derivation. The final tensor consumer derives irreducibility from reduced quotient and preservation/killing from the constructed fraction derivation. The actual integral Kahler frame, domain/DVR/fraction-field structures and precise quotient reducedness remain explicit geometric inputs.
8. History. Existing vertical scalar proofs handle rational prime uniformizers, and the previous reduced-quotient packet exposes the ramified-base limitation. This packet supplies the valid base-parameter generalization, not a complete semistable-model construction or a global all-place conclusion.
9. Validation. Exact prior module bytes and consumer hashes bind the application, together with pinned upstream sources. Static checks are structural only. Hosted strict checking, recursive private-inclusive axiom audit and distinct source acceptance remain pending; no self-approval is created.
