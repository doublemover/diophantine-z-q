# Actual global original-order unit lifts

Prove reduction of actual global units of the original maximal quaternion order onto every unit of literal O/3O and its projective quotient, and prove every finite norm-one unit has a global norm-one lift, retaining the distinction between full and positive units.

The explicit norm-minus-one generator is essential for the full72. Norm-one lifts are proved separately for the norm-one residue classes; the full36-element projective quotient is not mislabeled as the positive image.

## Application obligations

1. **Original global and local objects.** Required: Actual global original-order units, not abstract generators of a72-element finite group. Constructed: Three explicit integer-coordinate elements and their explicit inverse elements construct units in the same original order. The exact original reduced norms are minus one,one,one. The full reduction ring and literal O/3O equivalence are unchanged. Evidence: PELGlobalIntegralUnitLifts318.generator; generator_norm; generator_reduction.

2. **All finite classes.** Required: Every finite unit must be covered, with no assumed surjectivity of the global reduction map. Constructed: The actual words g^k*t^a*v^b have k inFin8 and a,b inFin3. All81 ring coordinates are considered. Nine radical elements contradict the explicit nonzero residue premise; all72 remaining elements receive literal original-word witnesses. Evidence: PELGlobalIntegralUnitLifts318.finite_cover; verification/check_unit_lifts.py.

3. **Exact signed reduction.** Required: A cardinality match does not identify the actual lift with the requested residue. Constructed: word_reduction proves equality under the original reduction hom for each specified global word. Exact finite_cover witnesses then give equality with the requested whole finite quaternion element. Evidence: PELGlobalIntegralUnitLifts318.word_reduction; PELGlobalUnitReductionSurjective318.unitReduction_surjective.

4. **Literal quotient and projective transport.** Required: Surjectivity must descend to the actual original quotient, not just its related presentation. Constructed: originalUnitReduction is Units.map of the actual O→O/3O quotient map. Injectivity of the existing quotient equivalence reflects the full unit equality. The actual signs quotient gives projectiveReduction and its surjectivity. Evidence: PELGlobalUnitReductionSurjective318.originalUnitReduction_surjective; projectiveReduction_surjective.

5. **Norm sign and positivity.** Required: Full72-unit surjectivity must not be attributed to norm-one units. Constructed: The first global generator has norm minus one. word_norm proves the original rational reduced norm is(-1)^k. The finite residue norm of that same word is(-1)^k inF3. The statements distinguish all global units from norm-one lifts. Evidence: PELGlobalNormOneLevelLifts318.word_norm; finite_word_norm.

6. **Actual norm-one lifts.** Required: Every finite norm-one unit must have a GLOBAL norm-one lift with exact same reduction. Constructed: The same exhaustive finite_cover supplies a word. Its given finite norm-one condition forces its explicit exponent k even. The original rational norm of that exact word is therefore one; no unrelated global unit or norm adjustment is postulated. Evidence: PELGlobalNormOneLevelLifts318.original_norm_one_lift.

7. **Polarization and arithmetic boundaries.** Required: Do not identify all markings with positive polarized family symmetries or assert canonical576 extension. Constructed: Full global units reduce onto72, while norm-one units lift exactly norm-one finite data. Projective full-unit surjectivity is onto36. No positive-family action for norm-minus-one units, parity-kernel identification, normalizer extension order, contact branch identification or algebraic PEL moduli realization follows here. Evidence: README.md; inherited historical-source-pins.json.

8. **Exact predecessor repairs.** Required: Do not discard failed evidence or revert authoritative shared producers. Constructed: All56 other predecessor sources copy reviewed57r2 exactly. The shared period quotient source copies authoritative analytic103r2 exactly. This includes the original Perfect finite-coordinate repair and the period scalar-map proof repair, without theorem or budget changes. Evidence: verification/SOURCE-COPIES.json; SHARED-REPAIRS.json.

9. **Validation and source applications.** Required: Executable computations do not replace hosted Lean or independent mathematical review. Constructed: Independent checker parses each emitted finite_cover proof branch and literal witness, checks both global inverse products, exact norms/reductions, all72 images and36 norm-one images. It separately checks full/projective sign counts. Units.map/Units.mapEquiv and quotient surjectivity use the actual original homs/groups. Static source/import/hash validation and audit controls pass; no local Lean. Evidence: verification/check_unit_lifts.py; inherited primary API snapshots.

## Validation and remaining joins

No local Lean. Hosted strict-module recursive audit and independent acceptance remain pending. This removes the earlier global-unit reduction surjectivity gap for this literal order, but does not establish parity-kernel equality, canonical normalizer/deck extension, algebraic PEL family or original contact moduli map.
