# Independent source review: three observed PEL frontiers

Reviewer: lean_review_resume. Run 43578868567 at published 977040de03da47698b89a3345d93e2ffcbc2220c. No local Lean/Lake/compiler execution. Review is source/provenance checking, not theorem or application acceptance.

## Verdict and identities
No source-level defect found in these three bounded candidates. They may be packaged for hosted checking. The revised Siegel route has been reviewed anew rather than inheriting acceptance from an earlier failing proof.

- ComplexCurveHomeomorphInverse318: d733011f5fed167cba8f34d2c79ff293b74edc51fbfaf484923ef8bd9889ca6f → 6f7940f20bcedfd70cb9a727211fa4d45e105f30ec98577e6967cb6543f4dfec.
- PELOriginalSiegelNormalization318: 8482d502e63537c9ce5027316619e5144316de673244f50fe455c47c4dfc37de → 82b08afe42657ec2a7d436686af328e42f9db2f8a430f6e772667cd6794650fc.
- PELActualOrderNormalizer318: 8fe62551ec1e115384e3649a44a416e440f5cd4ebbc724abfa19b40030262c24 → 6f67005a6c0065459da960faf85d3cc122898c4e26f7355afabad0eb33f724e3.

Contract APPLICATION.md: 0288f24d66b627c66ea059b776ad7552f29a89db5cf7cbe33b526784d670eb41.

## Homeomorphism inverse: exact composition
The sole edit explicitly supplies outer composition input f(z)=h(e.symm z). Read pinned ContMDiffAt.comp at Mathlib Geometry/Manifold/ContMDiff/Basic lines127–129: hg is evaluated at f x and hf is the same f. The intended outer map remains g, hence the result is the original chart map K, not a replacement inverse. Every p, original manifold structure, chart membership and holomorphy premise is retained. No nonvanishing derivative assumption is added. Actual consumers CompletedBiholomorph.inverse_holomorphic, OrderedCharacterBiholomorph.inverse_holomorphic and DenseComparison apply this exact theorem to their given homeomorphisms; inspected their bodies, not just imports.

## Siegel: complete revised algebraic route
The two inverse proofs now evaluate the actual two-coordinate vector projections with cons_val_zero and cons_val_one before clearing the SAME denominators. Pinned VecNotation gives these exact rfl identities. Both coordinates of every ComplexVectors element remain covered. Positivity hτ, parameter_ne and beta_complex_ne stay in the same scopes.

original_period now applies injectivity of the SAME normalization.symm and cancels its forward application. The remaining equality is exactly original periodHom(embed(fromPair p)) = denormalize(standardPeriod p). This is equivalent to the old goal and introduces no alternative lattice or period object. It is not circular: normalization is built from the preceding inverse proofs, neither of which uses original_period. Denormalize has numeric halves rather than beta inverses; omega still contributes τ inverses discharged using the existing parameter_ne. The ring calculation retains beta²=5 normalization and must prove both complete coordinates for EVERY integral Pair, not only four generators or a finite-index sublattice.

Read the literal normalize/denormalize, omega/standardPeriod usage and original latticeMap/latticeEquiv definitions. The local hl in denormalized_period identifies the coercion of latticeEquiv(fromPair p) with the SAME periodHom/embed expression. Pinned ofBijective_apply is rfl; the producer latticeMap.toFun has that exact value. `simp only ... <;> rfl` permits either simplifier closure or the residual definitional equality without a no-goals error. The final congrArg/symm direction gives denormalized_period as originally stated.

All coefficients, beta²=5, determinant convention, factors2/5/10, pi, Complex.I, phases, canonicalQuadratic, normalize/denormalize definitions and full original lattice are unchanged. Read GaugedTheta.period_exact, which consumes original_period at the actual label of every lattice element; ThetaHermitianGauge.exact_multiplier rewrites normalized_factor_formula. SiegelCoercivity.normSq_positive uses the unchanged positivity consequence parameter_ne. These are actual downstream applications. No later consumer pass is claimed.

## Actual normalizer: type-tag normalization only
The single `change` target now spells out underlying fiveLabels i instead of leaving a placeholder retaining Multiplicative.ofAdd. The public conclusion remains the original Multiplicative.ofAdd equality. Full two-sided normalizer subgroup, original rational inertia representatives, connecting-unit norm-one identity and all Fin5 labels/ordered words are unchanged. Read PositiveOrderNormalizer.parity_inertia, InertiaRationalConjugacy.inertia_parity and NormalizerParityQuotient.inertia_class: each consumes this exact map/equality. No restriction to prime generators, finite sample or selected inertia element is introduced.

## Nine-obligation contract and exact evidence
The contract distinguishes native inputs, constructed objects, full domains and exceptional cases, transition directions, exact output identities, direct consumers, coefficient/sign conventions, public/trust scope, and evidence boundaries. All existing public headers/formulas/imports/options remain unchanged this round, including previously restored positivity binders. No new premise, axiom, admission, resource increase or preventive change appears.

Independently checked CANONICAL-MANIFEST hashes, all three before/after bytes, all FIVE own log/RESULT/ZIP hashes, each RESULT packet hash against the exact published intake, and before sources against those exact git blobs. Verified all native primary file hashes and all ten consumer-evidence files against published git copies. Failed404 lookups are not cited as native declarations. Own evidence establishes these observed failures, not successor success; previous ChartInverse/NormParity passes do not confer acceptance on these downstream candidates.

Remaining risk is hosted elaboration and kernel behavior of the full algebraic and coercion proofs, plus later consumers. Successor exact-copy propagation, full packet checking, recursive axiom audit and independent arithmetic theorem acceptance remain separate and pending.
