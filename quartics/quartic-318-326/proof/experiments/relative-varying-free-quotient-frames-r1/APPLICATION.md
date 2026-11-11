# Application contract: actual free quotient frames

1. **source_requirements.** Required: Actions must be genuinely cyclic and the full annihilator ideals equal.

Constructed: equiv composes the actual quotientEquiv inverses with Ideal.quotientEquivAlgOfEq on those exact ideals.

Justification and boundary: No rank comparison or fibre equality replaces source ideal equality.

2. **constructed_objects.** Required: The claimed orbit relation must be actual invertible frame change preserving action and vector.

Constructed: frameRelation explicitly quantifies a linear equivalence, intertwining every algebra element on every module vector and preserving the marked vector.

Justification and boundary: The setoid equivalence laws follow only after proving this relation equals exact ideal equality.

3. **index_coverage.** Required: Intertwining and uniqueness must hold on the entire module.

Constructed: Cyclicity supplies an evaluation preimage for every module vector; evaluation_mul proves intertwining for every source element.

Justification and boundary: No finite generating vector subset or pointwise argument is substituted.

4. **transition_maps.** Required: Equal ideals must induce the same comparison on their literal quotient representatives.

Constructed: quotientEquivAlgOfEq_mk and quotientEquiv_mk prove exact evaluation preservation.

Justification and boundary: The canonical comparison is unique among all actual frame intertwiners, giving a basis for later overlap cocycles without claiming them here.

5. **hypothesis_checks.** Required: Every ideal quotient to be classified must actually be free of the stated rank.

Constructed: FreeIdeal contains Nonempty(Basis ι R(A/I)); fromBasis uses that basis to conjugate the actual quotient multiplication action.

Justification and boundary: No projective module is silently treated as globally free, and no basis is inferred from dimension.

6. **consumer_identity.** Required: The reconstructed framed representative must recover the original full ideal I.

Constructed: fromBasis_ideal uses the SAME quotient map, multiplication action, marked unit and basis equivalence, then exact Quotient.eq_zero_iff_mem.

Justification and boundary: The returned classifier maps the orbit to that full ideal subtype, not an isomorphism class of abstract rings.

7. **normalizations.** Required: Original-source actions must correspond to literal S⊗A actions without changing the source.

Constructed: fromFramedData is the inverse of the SAME AlgHom.liftEquiv on actual matrix coordinates. fromFramed_action and from_to_data prove both inverse directions.

Justification and boundary: Matrix/linear equivalences are used with exact inverse identities; the marked vector is unchanged.

8. **downstream_boundary.** Required: Set quotients and family scheme quotients are different conclusions.

Constructed: classifier is an Equiv on Quotient(frameSetoid); source_ideal_surjective recovers all free original-source quotient ideals.

Justification and boundary: Normalized word charts, overlap maps/cocycle, scheme gluing, locally free descent and Picard remain open.

9. **evidence_acceptance.** Required: New quotient/conjugation/adjunction applications need exact sources and consumers.

Constructed: Pinned conjugation source is added; existing ideal-quotient, basis, matrix and tensor sources are retained with605 ordered source hashes.

Justification and boundary: No local Lean was run; static checks are not proof acceptance. Fresh independent source review and hosted/kernel audit remain required.

