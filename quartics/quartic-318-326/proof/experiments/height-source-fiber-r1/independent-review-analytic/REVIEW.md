# Bounded non-author review: actual rational contact fiber

Decision: accept the exact three-source curve-level application described
below. Reviewer: `/root/advance_analytic_geometry`, distinct from the producer.
This is an internal model source review with an independent copied strict
replay, not an independent whole-proof audit.

## Source theorem to consumer checks

1. **Constructed objects.** `RationalFourRootFiber318.PointField` is the
   maximal residue field of the actual nested tensor product of four monic
   quadratic root algebras. `FourRootOrder318.rank_sixteen` applies for every
   rational coefficient tuple, including zero or dependent squareclasses.
   The positive rank establishes nontriviality before maximal-ideal existence
   is invoked. No generic irreducibility is substituted for a specialization.

2. **Finiteness and degree.** The quotient map is the original Q-algebra
   quotient homomorphism and is surjective. The finite-dimensional inequality
   is in the correct direction: the quotient field has dimension at most
   that of the rank-sixteen algebra. Mathlib's `NumberField.of_module_finite`
   requires a finite extension of a number field; Q and the quotient field
   with its actual algebra structure supply exactly those inputs. The
   cardinality of the geometric fiber is not confused with the residue-field
   degree.

3. **Complete sign orbit.** Equality of squared generator values gives
   equality or negation for each of all four roots over any field. The
   actual `signEquiv` and `hom_ext` then recover every algebra homomorphism.
   Injectivity uses nonzero root values and characteristic zero to separate
   the two signs. The point field need not be algebraically closed. The
   existing point already supplies all four roots, so all sixteen sign
   choices are defined over that same field. This proves the stated Hom-set
   cardinality, not an assertion that the field degree equals sixteen.

4. **Original base and coefficient map.** `RationalContactPoint318` specializes
   `ContactKummerOrder318.R = Q[t]` by the actual `Polynomial.aeval t`.
   Its local R-algebra instance on the residue field is the composite with
   the existing Q-algebra map. The explicit scalar tower matches that map.
   `FourRootSignBaseChange318.coefficientMap` is built from the original
   tensor base-change equivalence, and its four generator identities are
   consumed without changing the coefficient tuple.

5. **Scheme direction and downstream identity.** `Spec.map` reverses the
   actual source-order homomorphism, followed by
   `SourceGlobalAffine318.chartEmbedding`. The latter maps into the original
   normalized proper model. Its already proved contact-line square and the
   source point's scalar-commutation law prove `point_over_coordinate` as
   an equality of actual Scheme morphisms. Neither an abstract isomorphic
   curve nor only a field-valued coordinate equality replaces the consumer.

6. **Normalization and every branch.** The consumer uses t=32u/v. The
   original finite contacts are 0, 32, 76832, -343, matching the normalized
   five-form avoidance theorem at s=u/v. The four finite cases are explicit
   and exhaustive, and the same avoidance theorem supplies v nonzero for
   the infinity contact. Nonzero twist units and the injective Q-algebra map
   then give the stated nonzero coefficients and roots. No extra coprimality
   premise is needed for this point-construction statement.

7. **Exceptional scope.** The field and point constructions exist even at
   branch values. Only the nonzero-root and sixteen-point theorems require
   avoidance. Squareclass collapse is allowed, so the degree bound is an
   inequality. No normality, Galois property, discriminant, unramifiedness,
   good reduction or arithmetic integral model is inferred from it.

8. **History and changed-route boundary.** I read the earlier
   `progress/receipts/fiber-field-bridge/FIBER-PRODUCER.md`, including its
   actual whole principal-level-three torsor and separate integral-support
   arguments. That historical degree-dividing-576 normal splitting field
   is different from this chosen degree-at-most-sixteen contact residue
   field. The packet correctly keeps them separate. This review does not
   independently accept the external canonical-model, PEL, stable-model,
   KS, CM or Arakelov applications listed in the status document. Their
   absence as new Lean constructions is not classified as a newly found
   mathematical gap.

9. **Exact validation.** I copied all three frozen sources into a separate
   review directory, compared their hashes with the producer receipt, and
   compiled them using Lean 4.35.0 with `-j1 -M6144
   -Ddebug.skipKernelTC=false`. A fresh private-inclusive recursive audit
   reports `EXPERIMENT_AUDIT_PASS declarations=43 modules=3`, allowing only
   `propext`, `Classical.choice` and `Quot.sound`. The actual required
   predecessor source pins were checked against the admitted checkout.
   This replay reused verified predecessor objects; it was not a clean
   rebuild of their transitive proof sources.

## Accepted endpoints and remaining work

Accepted: the actual bounded number field and roots; the complete literal
sign orbit; the actual source-order and original proper-model point; its
exact map to the supplied rational coordinate; and the four nonzero-root
and sixteen-point specializations at the literal five-form input.

Not accepted or claimed: a PEL identification of the twist tuple, a universal
abelian surface or marking, a degree-576 field, ramification support,
canonical/Hodge/KS identification, CM/non-CM realization, or
`FiveContact49Height`. The independent acceptance is bound to the exact
source, producer receipt and application-contract hashes in `acceptance.json`.
