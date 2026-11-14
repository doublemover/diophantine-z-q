# Independent source review of observed PEL frontiers, run43519890754

Reviewer lean_review_resume. Exact source comparison against hosted run43519890754, head58753ec5f3b41268c5ceedae5264593b4f2aa0de. No local Lean/Lake, user-PC access, push or proof acceptance. This review covers canonical candidates, not yet successor propagation.

## Bound sources
- FourRootAffineCoordinateRing318.lean: before889e39049b77a2083007f60c5cb55da0d297197d5f2edbc37c5ea79e769520c0, after42d0cf571e5a1a5d341d862cec973295c7538fc007dce0d51c40649fab81ee7c.
- PELOriginalPolarizationMetric318.lean: beforef6e47e1d1f217ebf47eb3123d14941e97a4d882026dd890e536183b3f4be3d16, after454a20b1d039133198f7300c3e7bbd2efbce083cb4f80293e85e41ff4387510a.
- PELLevelThreeAlternatingPair318.lean: before925f7ce420cd06ec94d079b370d576eceae33ebdc2e7c72a5585822b2d3eed1c, aftera03d3ec0eca7533ae921042fe27e2b1099419d4ce1959e609cb08e4f7c8586dd.

Read full before/after sources, diffs and exact corresponding logs: affine in zero-local-length-r32/cotangent-r38; metric in torsion-towers-r12; alternating pair in normal-trace-r5/character-r5. Checked pinned quotient and multivariate evaluation source plus original action/coordinate/reduction definitions.

## Affine quotient evaluation
The hosted residual is the actual quotient lift evaluated at the actual quotient image of X k; the general simp did not match lift_mk. The candidate changes that definitionally equal expression to aeval (fun j => Option.elim j t z) (X k), then applies MvPolynomial.aeval_X. Pinned Quotient Defs exposes the lift and proves lift_mk by rfl. Quotient Operations lift_algebra application is also rfl; the candidate does not need a new quotient theorem. The pinned aeval_X has the two explicit arguments f and s, so the two placeholders infer the displayed evaluator and k. It retains arbitrary original complex algebra S, all four defining equations and every Option(Fin4) coordinate; no new premise or coordinate change.

## Metric action
Exact log reports ambiguity between the automorphy action and QuaternionicRealPeriod matrix action in the simp set. The goal itself already displays PELOriginalPolarizationAutomorphy318.action. Both statement and simp now explicitly name that same action, whose exposed body is (p.1+l.val, factor*l scalar). Weight, positive Riemann sign, squared norm, lattice input and factor_metric are unchanged. This is qualification, not selecting a different action.

## Alternating pair
Exact log shows generic reverse map_mul tried to use the additive coordinatesEquiv as a multiplicative map, creating an invalid MulHomClass and pointwise a*b. The candidate first applies map_mul specifically to moduloThree.mk_prime, the original quotient ring hom, separately on the left and Rosati-right products. Only afterward does it invoke coordinates_mul a b and coordinates_mul (involution a) c. Read the original coordinates_mul: it relates the explicit quaternion-coordinate product, not pointwise coordinate multiplication. Therefore the new proof targets the intended noncommutative order product and uses integral_adjoint with the same product/involution.

The proof still obtains every order coordinate and every quotient representative by the same surjections. The pair is still on actual O/3O and retains original_pair's negative integral Riemann sign. No index, exceptional case, order action or Rosati map is weakened.

Conclusion: no source-level blocker in these exact three candidates. Public intended statements, imports and resource options unchanged. Hosted strict elaboration and downstream axiom checks remain required; source reasoning alone does not prove the modules pass.
