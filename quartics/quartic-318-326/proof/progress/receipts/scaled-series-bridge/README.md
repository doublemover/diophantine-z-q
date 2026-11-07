# Actual integral scaled-series bridge

This isolated package supplies actual coefficients, not abstract series chosen to satisfy a group law. It does not modify the repository or the evaluation worker's files.

## Hypotheses and normalization

Let p be prime, p ≥ 19, and D ∈ Q_p with ‖D‖ ≤ 1. All statements allow D=0. Define κ = D p⁴ and

- h_j = choose(2j,j) / [4^j(4j+1)], exactly `HCoefficients318.coefficient j`;
- b_j = choose(2j,j) / 4^j, exactly `FormalDifferential318.b j`;
- c_j = h_j D^j p^(4j), d_j = b_j D^j p^(4j).

## Kernel-checked modules

`ScaledCoefficients318.lean` proves c_j,d_j are in Z_p, constructs `Hscaled` and `Bscaled` from those coefficients by `PowerSeries.mk`, and proves their exact coefficient-map identities:

- `map_Hscaled`: Hscaled ↦ rescale κ (GenericFormalDifferential318.H).
- `map_Bscaled`: Bscaled ↦ rescale κ (GenericFormalDifferential318.B).

The proof first uses the independently checked source coefficient valuation lower bound, then clears its denominators. It never divides an integral-ring residue.

`ScaledFormalSeries318.lean` constructs, over Z_p,

- `parameter p D hD = (D.lift hD) * p⁴`;
- `integralScaled = -X * Hscaled.subst(X⁴)`;
- `differentialScaled = Bscaled.subst(X⁴)`;
- `branchScaled = (1-C(parameter)*X⁴) * differentialScaled`.

It proves exact coefficient-map bindings to `GenericFormalDifferential318.integral`, `.differential`, and `.branch` at κ, plus constant coefficients 0 and 1 for the integral and branch. `formal_addition` then instantiates `IntegralFormalAddition318.formal_addition` using the actual injective inclusion Z_p → Q_p. Consequently its conclusion is the full two-variable formal identity for these actual scaled series. It does not assume an additive-logarithm or group-law identity.

`ScaledDecay318.lean` strengthens integrality to uniform geometric decay. The elementary inequality 4j+1 < p^(j+1) gives v_p(h_j) ≥ -j for every j. Therefore

- `hCoefficient_decay`: ‖c_j‖ ≤ (‖p‖³)^j;
- `bCoefficient_decay`: ‖d_j‖ ≤ (‖p‖⁴)^j.

Both ratios are strictly below 1. Theorems `h_summable`, `b_summable` prove actual summability for every t ∈ Q_p with ‖t‖ ≤ 1. Theorems `Hscaled_summable`, `Bscaled_summable` state the same convergence using coefficients of the constructed Z_p power series, for every t ∈ Z_p, including units.

## Closed-disc evaluation and inert completion

`RestrictedEvaluation318.lean` now proves actual closed-unit-disc evaluation/composition for arbitrary restricted power series over Z_p, including unit arguments. Evaluation is the genuine monomial tsum. The proof constructs an unconditionally summable double family, proves Cauchy products and powers, and interchanges the sums. `eval_subst` assumes only restrictedness of the two input series and zero constant coefficient of the inner series. It assumes no logarithm law.

`ScaledClosedDisc318.lean` proves restrictedness of the actual scaled H/B, integral, differential, and branch series, and their exact evaluated formulas. `GeometricInverse318.lean` proves that the source formal inverse of 1+C(a)X⁴ is restricted when ‖a‖<1 and evaluates to the ordinary field inverse at every integral argument.

`IntegralRingEvaluation318.lean` generalizes these evaluation/composition proofs to a complete ultrametric commutative normed ring whose elements all have norm at most one. It uses only submultiplicativity of the norm, not norm multiplicativity. `InertClosedDisc318.lean` first instantiates the evaluator on the actual inert ring and covers the Q_p-parameter subfamily. That subfamily alone does not include the literal inert curve parameter. `IntegralScaledSeries318.lean` therefore constructs the coefficients for arbitrary D in the integral ring by rescaling the embedded D=1 series, proves their exact coefficient-map bindings and formal addition, and imposes no descent-to-Q_p condition. `ArbitraryInertSeries318.lean` instantiates that stronger interface and explicitly constructs the literal source D=11−6√2, proving restrictedness and genuine convergent evaluation for it at all inert units. `IntegralGeometricInverse318.lean` supplies the corresponding geometric inverse over the same generic ring interface. `FormalSeriesNaturality318.lean` separately proves exact field-map naturality of the original H, B, integral, differential and branch series.

`IntegralScaledBounds318.lean` proves, for arbitrary integral D and every integral argument, H−1 bounded by ‖p‖³ and B−1 and V−1 bounded by ‖p‖⁴. It obtains genuine units via the complete-ring Neumann-series criterion, nonzero images in any nontrivial ambient ring, and quantitative near-one bounds under isometric ambient embeddings. These include the actual inert parameter and units. `IntegralScaledNorm318.lean` strengthens these conclusions to exact norm one in the integral ring and every isometric ambient inclusion, for direct logarithm-isometry use.

## Remaining assembly scope

This package does not itself complete every source/group-law parameter binding. The analytic worker owns the formal two-variable pullback, actual canonical-root identification, rational source parameter identities, and final soundness assembly. The earlier analytic composition blocker at depth one is closed by the modules above; it is not silently replaced by an assumed group law.

## Reproduction

Run `./build-all.sh` from this folder or its parent. The script uses the already-installed Lean 4.35.0 environment and module dependencies in `padic-tail`, sets `-Ddebug.skipKernelTC=false`, and emits isolated `.olean` files. `build.log`, `build-restricted.log`, `build-generic.log`, and `axiom-audit-all.log` record the runs. The full audit checks every one of the 172 public theorems in the 15 modules. All printed theorem axiom roots are limited to `propext`, `Classical.choice`, and `Quot.sound`; there are no theorem-specific axioms or sorry placeholders.

## Arbitrary-input local square root

`IntegralSquareRoot318` proves the exact formal and evaluated B-square identity at every integral argument, not just fourth powers. Its constructed root `(1−θt)eval(B,t)` squares to `1−θt`, differs from1 by norm at most `‖p‖⁴`, is a genuine unit, and has norm1. This is the input used for actual inert affine-chart membership.
