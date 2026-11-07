# Actual E4 cusp-series producer

Strict kernel replay and recursive audit pass: one module, 12 declarations (nine public theorems), standard axioms only.

## Actual object and exports

`E4Producer318.E4` is exactly `UpperHalfPlane.cuspFunction 1 (ModularForm.E (k := 4) ...)`. It is the actual normalized Eisenstein series from Mathlib, not an arbitrary function satisfying a coefficient hypothesis.

- `E4_holomorphic`: differentiable over C on the open unit disc.
- `E4_zero`: its value at the cusp is one.
- `E4_qParam`: evaluating at the genuine periodic q-parameter returns the actual weight-four modular form.
- `E4_coeff` and `E4_hasSum`: the genuine q-expansion coefficients and their convergent sum on the entire unit disc.
- `sigma_series_summable` and `E4_series`: absolute convergence and the exact identity `E4(q)=1+240 sum sigma_3(n) q^n`, including q=0 (sigma_3(0)=0).
- `fourth_moment_hasSum`: the exact majorant sum at radius 1/100.
- `E4_bound`: `norm(E4(q)) < 4` whenever `norm(q) <= 1/100`.

## Bound and identification

The actual q-expansion is obtained from Mathlib's `EisensteinSeries.E_qExpansion_coeff`, with Bernoulli(4) evaluated exactly as -1/30. The standard modular-form cusp API supplies holomorphicity and binds the value to the genuine Eisenstein series. No coefficient-identification premise remains.

The estimate uses the correct divisor bound `sigma_3(n) <= n^4`. It does not use `sigma_3(n) <= n^3`. Mathlib's actual power-geometric summation theorem, evaluated at fourth power and radius 1/100, yields

    sum n^4 (1/100)^n = 37036700 / 3169966833.

The exact positive majorant `1+240*37036700/3169966833` is strictly below four. HasSum's norm comparison gives the result without interchanging an unjustified limit or overlooking the constant term. The zero-coordinate case is included.

## Scope

This fully closes the E4 coefficient, convergence, holomorphy and small-disc norm input. The Euler product, modular discriminant identity, actual q*j identity, and downstream G bound are separate work. No claim about those objects or the entire five-contact theorem is made by this module.

Run `bash run.sh`. The scripts reuse the installed Mathlib cache and strictly rebuild the actual module and exhaustive audit. No repository or Git operation was performed.
