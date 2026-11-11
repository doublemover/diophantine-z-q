# Application contract: canonical source-action parameter

1. **source_requirements.** Required: Actual commutative R-algebra A and every coefficient R-algebra S, including nonreduced and zero rings.

Constructed: Index uses every a∈A plus every scalar r∈R and all matrix entries.

Justification and boundary: The canonical presentation may be infinite; no finite generating family is assumed.

2. **constructed_objects.** Required: Source relations must enforce a genuine original-algebra homomorphism, not merely commuting generators.

Constructed: Explicit zero, one, add, mul and scalar entry equations define a quotient of the SAME commuting matrix/vector ring.

Justification and boundary: The action constructor proves every AlgHom field directly from the corresponding relation.

3. **index_coverage.** Required: Every original source element, pair and coefficient must occur in the equations.

Constructed: Index constructors range over all A, A×A, R and ι×ι.

Justification and boundary: There is no finite word cutoff, radical quotient or geometric-point restriction.

4. **transition_maps.** Required: Coefficient change must preserve the actual equations.

Constructed: equation_map checks each constructor using finite sums, products, zero/one and exact scalar-map commutation; valid_map transports all relations.

Justification and boundary: The two-sided parameter equivalence uses the original quotient and its actual universal lift.

5. **hypothesis_checks.** Required: Base change must produce an S-linear algebra action of S⊗[R]A.

Constructed: Pinned AlgHom.liftEquiv extends the constructed R-algebra map to matrices over S; the actual matrix/linear-endomorphism equivalence supplies linearAction.

Justification and boundary: Its tmul formula retains the coefficient s and original source element a exactly.

6. **consumer_identity.** Required: The word determinant must be formed from the SAME action used to construct the quotient.

Constructed: word_evaluation identifies each literal source-product tensor with the original recursive matrix word. Cyclicity uses exactly these image columns.

Justification and boundary: The finite-flat consumer is CyclicQuotientFiniteFlat318 on that same linearAction and marked vector.

7. **normalizations.** Required: The scheme-theoretic source ideal and full coefficient module must be retained.

Constructed: quotientRing is the full vector-annihilator ideal quotient of literal S⊗[R]A, and quotientBasis transports the standard S^ι basis.

Justification and boundary: No reduction, field extension, generic fibre or dimension-only argument is substituted.

8. **downstream_boundary.** Required: Framed-action representability is not yet the global varying-quotient or Picard classifier.

Constructed: The construction represents source actions; selected unit determinants yield actual finite-free source quotients.

Justification and boundary: Cyclic-open representation inside this parameter, cover completeness, frame quotient/gluing, locally free descent and Cartier/Picard remain separate.

9. **evidence_acceptance.** Required: New theorem applications need exact sources and fresh independent acceptance.

Constructed: Pinned matrix algebra, tensor base-change adjunction and basis sources are bound alongside all595 ordered Lean files.

Justification and boundary: Static checks do not prove elaboration or kernel validity. Independent source review and hosted Lean/axiom audit remain pending.

