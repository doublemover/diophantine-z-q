# Application contract: actual varying cyclic quotient foundation

1. **source_requirements.** Required: The source A and coefficient R are commutative rings; M is an R-module with an ACTUAL R-algebra action rho:A→End_R(M), a vector v, and explicit cyclic-surjectivity when constructing the quotient equivalence.

Constructed: CyclicQuotientEvaluation318 constructs the R-linear evaluation and its ideal; CyclicQuotientKernel318 requires exactly that surjectivity.

Justification and boundary: No commuting-matrix family or cyclicity is assumed to have been constructed from finite coordinates. Those remain named prerequisites.

2. **constructed_objects.** Required: The annihilator must be an ideal of the entire source algebra, not only an R-submodule.

Constructed: evaluation_mul gives the exact multiplication identity; ideal.smul_mem uses that identity.

Justification and boundary: Restricting scalars identifies its full underlying R-submodule with the evaluation kernel by extensional equality.

3. **index_coverage.** Required: Statements must hold on arbitrary coefficient rings, with every vector and every source algebra element.

Constructed: All a∈A are quantified; no field, domain or reducedness instance is present. Matrix coordinates use an arbitrary finite basis.

Justification and boundary: No claim of a determinant cover is made: obtaining cyclicity from local word bases is the next distinct step.

4. **transition_maps.** Required: Frame changes must preserve the full source action and marked vector.

Constructed: CyclicQuotientIntertwiner318 consumes a genuine linear equivalence e, intertwining all rho(a), and e(v)=w.

Justification and boundary: Evaluation is transported pointwise for every a; injectivity of e proves equality of actual ideals, and surjectivity transfers through e.symm.

5. **hypothesis_checks.** Required: The module first-isomorphism theorem requires surjective linear evaluation; scalar restriction must match exactly.

Constructed: quotientEquiv composes the inverse restrictScalarsEquiv, quotEquivOfEq for the proved kernel identity, and quotKerEquivOfSurjective.

Justification and boundary: The quotient-basis construction maps the SAME basis through this isomorphism; finite and free instances are derived from that basis, and flatness from freeness.

6. **consumer_identity.** Required: The resulting family must be the quotient of the original source by the actual kernel, not a surrogate abstract finite algebra.

Constructed: OriginalFreeQuotientAction318.action is multiplication after the original algebra map; evaluation at1 is literally q(a).

Justification and boundary: ideal_eq_kernel identifies the entire original kernel; originalQuotient_mk exposes the exact quotient map. ContactVaryingAffineQuotient318 specializes to the literal original finite/infinity tensor rings.

7. **normalizations.** Required: No radical, saturation, scalar rescaling, rank truncation or passage to closed points may replace the ideal.

Constructed: matrix_vector_zero_iff identifies matrix/vector vanishing with membership in the same actual ideal.

Justification and boundary: Matrix multiplication is the same algebra action in the same basis. A frame change must satisfy all-algebra-element intertwining; no insufficient generator criterion is substituted.

8. **downstream_boundary.** Required: Varying quotient geometry needs represented parameter charts, cover completeness and transition gluing before any representability conclusion.

Constructed: This packet produces a finite-flat closed affine family FROM supplied cyclic representation data only.

Justification and boundary: It does not represent those data, prove a word determinant cover, glue the two original affine charts, identify a Cartier locus, form linear equivalence, or construct a Picard/Jacobian. The575 fixed-line producers remain unchanged.

9. **evidence_acceptance.** Required: New source requires exact binding, pinned source comparison, independent review and hosted elaboration before acceptance.

Constructed: PRIMARY_SOURCES.json pins the actual linear quotient/matrix/first-isomorphism APIs; intake/order/hash/audit files bind all582 Lean sources.

Justification and boundary: Static checks do not check theorem truth or elaboration. No independent acceptance is authored here; no local Lean was run.

