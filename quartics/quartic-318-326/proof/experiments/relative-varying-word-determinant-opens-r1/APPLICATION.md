# Application contract: represented word-determinant opens

1. **source_requirements.** Required: Commutative coefficient rings, finite basis index iota, an arbitrary source-generator index sigma, and all finite words.

Constructed: wordVector uses the literal recursive matrix action including the empty word; a chart index is an entire tuple iota→List sigma.

Justification and boundary: No fixed word-length cutoff or completeness premise is hidden.

2. **constructed_objects.** Required: The actual same parameter ring and its determinant element must be used.

Constructed: delta is the determinant of the original word columns in the universal commuting-matrix data; ring is Localization.Away delta.

Justification and boundary: The localization represents unit determinants on full rings, not merely nonzero determinants at geometric points.

3. **index_coverage.** Required: Cyclicity must mean surjectivity onto every vector of the original module.

Constructed: LinearEvaluationDeterminant318 explicitly expresses any target vector as an R-linear combination of the SAME image columns using the inverse determinant matrix.

Justification and boundary: The proof works also over the zero ring and for empty basis indices; no rank positivity or field assumption is introduced.

4. **transition_maps.** Required: Coefficient maps must preserve literal word vectors and determinant.

Constructed: wordVector_map follows every recursive matrix multiplication; determinant_map maps the actual determinant.

Justification and boundary: The open point equivalence uses the original localization inclusion and lift; Spec reverses this same map to a base-preserving open immersion. No frame transition theorem is asserted yet.

5. **hypothesis_checks.** Required: Nonsingular inverse requires a unit determinant over the ring, not nonvanishing.

Constructed: The point subtype has IsUnit of the actual word determinant; fromPoint uses exactly that unit condition with Away.liftAlgHom.

Justification and boundary: Cyclic-surjectivity is proved by full inverse-matrix computation, not required again after the word-unit condition.

6. **consumer_identity.** Required: Word columns used for the determinant must equal those of the original source-algebra evaluation.

Constructed: wordVector_original identifies them with the coordinates of rho applied to literal List.map g products and the original vector.

Justification and boundary: OriginalWordBasisCyclicity318 applies the generic determinant surjectivity theorem to exactly evaluation rho v and those products.

7. **normalizations.** Required: No pointwise rank, radical ideal or basis substitution may replace the original data.

Constructed: The basis is the supplied actual basis, the word tuple is retained, and localization is at the unmodified determinant.

Justification and boundary: The constructor does not quotient the frames, select a field basis globally, or drop nilpotent structure.

8. **downstream_boundary.** Required: Universal source quotient classification still needs original source relations and an action on the universal module.

Constructed: These are represented opens of the commuting-data parameter; cyclicity is discharged only when an actual source action is already present.

Justification and boundary: No claim of cover completeness, frame-overlap cocycle, global gluing, locally free descent, Cartier locus or Picard representability is made.

9. **evidence_acceptance.** Required: New applications must bind exact sources and distinguish static checking from Lean proof acceptance.

Constructed: Pinned nonsingular matrix, polynomial quotient and localization sources are included; all590 modules are ordered and hashed.

Justification and boundary: Static checks do not establish elaboration or proof validity. Independent source review, hosted Lean and recursive axiom audit remain pending.

