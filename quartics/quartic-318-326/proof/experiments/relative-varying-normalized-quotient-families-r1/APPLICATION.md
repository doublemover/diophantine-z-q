# Application contract: Recover normalized universal quotient families

1. **source_requirements.** Required: A universal family must be a quotient of the actual source algebra.

Constructed: The normalized universal frame acts on N^ι via the literal N tensor_R A action; quotient is by its whole annihilator ideal.

Justification and boundary: No commutative polynomial proxy, radical or fixed source-line quotient is substituted.

2. **constructed_objects.** Required: The family must carry the same normalization basis as the chart.

Constructed: basis_word proves that every selected source word image equals the explicit quotientBasis element.

Justification and boundary: Uses actual evaluation normalization and quotientEquiv_mk, not a separate rank/basis-existence argument.

3. **index_coverage.** Required: All word indices and arbitrary rings must remain.

Constructed: Every word tuple w and original R-algebra A with finite coordinate index ι.

Justification and boundary: No reduction, field condition or exclusion of nilpotents. All coefficient rings on overlap tests remain arbitrary.

4. **transition_maps.** Required: Overlap families must agree on the original ideal, not only up to an abstract module isomorphism.

Constructed: transition_ideal identifies the exact two annihilator ideals inside S tensor_R A.

Justification and boundary: Consumes the actual frame_transition and normalize_ideal; no equality after passage to radicals or residue fields.

5. **hypothesis_checks.** Required: Finite flat closed family hypotheses must be supplied.

Constructed: The universal normalized frame is cyclic on N^ι and standardBasis is an actual finite basis.

Justification and boundary: CyclicQuotientFiniteFlat supplies the closed immersion and finite/flat projection for precisely that action/vector.

6. **consumer_identity.** Required: The next consumer must use the same full quotient and original elements.

Constructed: quotientEquiv is Ideal.quotientEquivAlgOfEq for transition_ideal, and quotientEquiv_mk fixes all original elements.

Justification and boundary: This identifies full quotient algebras on pointwise overlaps, not an unrelated abstract free module.

7. **normalizations.** Required: Retain exact source-word and inverse-frame conventions.

Constructed: Universal basis is 1 tensor product(w_j); transition uses the inverse v-word frame.

Justification and boundary: The equality of ideals is directed from transitioned v-frame to the old w-frame; quotientEquiv follows that same direction.

8. **downstream_boundary.** Required: Pointwise ideal compatibility is not yet descent of universal families.

Constructed: Actual chart families and pointwise overlap quotient equivalences are constructed.

Justification and boundary: Base-change identification, global family descent and correct-image global scheme classifier remain open. Locally free quotients need not be globally free.

9. **evidence_acceptance.** Required: Evidence and scope must be separately reviewed.

Constructed: Exact629 predecessor modules plus two new sources and current bindings.

Justification and boundary: Static checks, independent source/API review and hosted Lean/recursive-axiom validation are distinct. No local Lean/profiler.

