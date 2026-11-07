# Tame formal-coordinate linearization

This packet proves the finite-order tangent-faithfulness ingredient using actual Mathlib power series, substitution algebra homomorphisms, finite sums and compositional inverses. It does not assume tangent faithfulness or introduce a formal-curve axiom.

For a field k and F in k[[X]] with constant coefficient zero, `sigma F hF` is the actual substitution endomorphism P↦P(F), and `orbit F hF n` is its nth iterate on X.

## Tangent one

`TameCoordinate318.finite_order_tangent_one` proves F=X from:

- constantCoeff F=0;
- coeff 1 F=1;
- `(n:k)≠0`;
- the actual nth substitution iterate on X equals X.

The condition `(n:k)≠0` says precisely that the finite period is invertible in the field. It also excludes n=0. No characteristic-zero hypothesis is needed. The proof forms the actual average

    H = (1/n) sum_(0<=j<n) sigma^j(X).

It proves H0=0, H1=1 and H(F)=H. The actual `PowerSeries.substInvOfIsUnit` exists for H. Applying its substitution identity gives F=X. The chain rule for actual formal differentiation proves the linear-coefficient formula used to check the average.

`finite_substitution_tangent_one` exposes the hypothesis directly as iteration of `PowerSeries.subst F`, without requiring clients to unfold the algebra-hom wrapper. `finite_substitution_tangent_one_charZero` specializes to any positive finite period in characteristic zero.

## General tangent character

`TameLinearization318.tangent_period` proves lambda^n=1 for lambda=coeff 1 F from the actual period. Weighted averaging forms

    H = (1/n) sum_(0<=j<n) lambda^(-j) sigma^j(X).

The parameter has H0=0, H1=1, and `parameter_eigen` proves H(F)=lambda*H. `conjugated_linear` uses the actual compositional inverse to prove

    H(F(H^(-1)(X))) = lambda*X.

`exists_linearizing_parameter` removes a separate nonzero-tangent hypothesis: the nonzero period and lambda^n=1 already imply lambda≠0. Its only hypotheses are constantCoeff F=0, the invertible period and the actual periodicity on X.

## Boundary

This proves the equal-characteristic, constant-zero formal-coordinate algebra used for tame stabilizers. The actual identification of a completed local ring of a smooth curve with k[[X]], the action as continuous substitution, and the stabilizer's finite tame order remain separate geometric inputs. It does not prove the harder mixed-characteristic shifted-constant special-point chart claim. In characteristic dividing n, averaging is unavailable and the theorem deliberately does not apply.

## Replay

Run `bash build-all.sh`. Both modules and every generated/private declaration are recursively audited with Lean4.35, `debug.skipKernelTC=false`, allowing only propext, Classical.choice and Quot.sound. The receipt pins all accepted sources/logs. No repository or other worker's file was edited.
