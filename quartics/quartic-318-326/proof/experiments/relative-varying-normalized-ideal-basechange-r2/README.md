# Prove exact quotient ideal base change

633-source candidate: exact631 plus2 modules.

The normalized word basis gives an explicit linear section of evaluation. The defect of each original source element, 1 tensor a minus its word-basis expansion, generates the entire annihilator ideal. Tensor induction proves full generation, including nonreduced rings. Coefficient maps preserve both evaluation and the explicit section, hence preserve these exact generators. Ideal.map of the old full ideal is therefore exactly the full ideal of the coefficient-changed normalized point, with no flatness or surjectivity assumption.

This supplies the missing ideal-level universal-family base-change compatibility. Actual quotient tensor-algebra/scheme base-change comparisons, global family descent and the correct-image global classifier are separate next steps.

No local Lean or profiler executed. Static checks and independent source review are separate from hosted Lean/kernel/axiom acceptance. Frozen598/core remains unchanged.


## Exact240 immutable elaboration successor

Exact240 first full/core runs reveal two elaboration failures. The full lane still reaches original overlap coordinates, whose RingHom annotation selects semiring structures incompatible with inferred additive-monoid-algebra/tensor-product coercion structures. The same algebraMap is now constructed with all class arguments explicit and applied by its direct toFun projection, avoiding a second RingHom coercion expected type. Both coordinate values and square proofs are unchanged. The core reaches CyclicQuotientEvaluation.ideal: rw cannot see through set-builder membership in add_mem. The proof now explicitly changes both hypotheses and target to evaluation equalities; smul_mem similarly exposes its membership hypothesis. No ideal, carrier, action, theorem statement, hypothesis or budget changes;631 other sources exact. Hosted validation remains required.
