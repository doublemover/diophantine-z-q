# Actual qj analytic producer

This packet proves the regularized modular-j function inputs used by the cusp estimates from actual normalized Eisenstein series, Dedekind eta, convergent Euler products and the Mathlib modular discriminant. G is explicitly constructed; no holomorphy, constant coefficient, uniform norm bound or modular-form identification is supplied as an analytic premise.

## Actual functions and normalization

The consumed `E4Producer318.E4` is the actual cusp function of `ModularForm.E` at weight four, with its genuine divisor-sum q-expansion. The independently audited E4 packet proves holomorphy on the unit disc, E4(0)=1 and |E4(q)|<4 on |q|<=1/100. Its coefficient estimate is sigma_3(n)<=n^4, not the incorrect n^3 bound.

`EulerProduct318.product q` is the actual infinite product over n>=0 of `(1-q^(n+1))`. Mathlib supplies local uniform convergence and holomorphy. This packet proves nonvanishing on |q|<1 and the exact constant value one at zero. The already checked actual logarithmic-product estimate from `CMEta318` gives

    -log |product(q)| <= |q|/(1-|q|)^2.

On the closed radius-1/100 disc this implies `|product(q)^(-24)|<2`. The product is not replaced by an unverified formal approximation. `discriminant_qParam` binds it to Mathlib's actual eta^24 discriminant:

    Delta(tau) = q(tau) * product(q(tau))^24.

The normalized analytic j-invariant is explicitly defined by

    jInvariant(tau) = E4(tau)^3 / Delta(tau).

This is the standard normalization with leading term q^(-1), without an extra factor1728. `ActualJInvariant318.modular_invariant` additionally proves its invariance under the actual integral modular-group image in GL(2,R), using the genuine weight4 and weight12 transformation laws.

## Actual regularization

`ActualQJ318.G q = E4(q)^3 / product(q)^24`.

The packet proves:

- `G_zero`: G(0)=1;
- `G_holomorphic` and `G_differentiableAt`: holomorphic on the whole unit disc, including zero;
- `G_bound`: |G(q)|<128 for |q|<=1/100;
- `G_qParam`: G(q(tau))=q(tau)*jInvariant(tau);
- `cusp_G_data`: exactly the holomorphy/weak128-bound/constant-one tuple consumed by the cusp estimates;
- `selected_value`: the actual equation jInvariant(tau)=1728*(2^128+i) gives the required regularized value equation.

The value128 follows from 4^3*2. It includes a genuine product denominator nonvanishing proof. No totalized zero-division or log-zero convention is used to manufacture the analytic estimate.

## Boundary

The link between this genuine normalized analytic modular j-invariant and the user's actual algebraic/moduli j-map, together with existence and identification of the appropriate modular curve, its selected fiber and cusp uniformization, remains a geometric producer. A separate worker is binding the normalized Weierstrass c4/discriminant/j formulas. This packet does not substitute an unrelated function for j, but it also does not claim to construct a full algebraic modular curve or prove `FiveContact49Height` by itself.

## Replay

Run `bash build-all.sh`. It uses the installed Lean4.35/Mathlib pin and frozen `cm-height-producer` plus `eisenstein-four-bridge`. Strict kernel type checking is enabled. The exhaustive recursive audit checks every declaration in all three modules, including generated/private declarations, allowing only propext, Classical.choice and Quot.sound. Accepted files and dependency hashes are pinned in the receipt. No repository or other worker's files were modified.
