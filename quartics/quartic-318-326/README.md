# 318- and 326-variable quartics

The 318-variable quartic and its 326-variable smaller-coefficient companion for defining the integers in the rationals:

$$q \in \mathbb Z \iff \exists w \in \mathbb Q^{m-1},\; P(q,w)=0.$$

Here $m$ counts all variables, including the input. Both polynomials are primitive sums of squares: 288 quadratic residuals for 318 variables, and 296 for 326.

| Result | Total variables, including input | Witnesses | Degree | Monomials | Largest absolute coefficient |
|---|---:|---:|---:|---:|---|
| [318](results/318/polynomial.json) | 318 | 317 | 4 | 3,134 | 64 · 3^(2^17) |
| [326](results/326/polynomial.json) | 326 | 325 | 4 | 3,157 | 3^2048 + 3,813,373,282,171 < 2^3247 |

Coordinate 0 is the input. The 318 polynomial uses the fixed integer S = 3^(2^16). The 326 construction replaces S with seven uniquely determined squaring-chain coordinates and one product coordinate, keeping every residual quadratic.

Complete decimal coefficients: **[318](results/318/coefficients.txt)** ([JSON](results/318/coefficients.json)) and **[326](results/326/coefficients.txt)**. [The manifest](results/manifest.json) records their counts and hashes.

## Repository

- `results/318/`, `results/326/`: coefficient tables, quadratic systems, coordinate maps, and compiler certificates.
- `construction/`: source builder, affine shear, constant lift, and intermediate systems.
- `proof/318/`: Lean polynomial/source equivalence and exact degree-four proof.
- `proof/components/`: the original 50 Lean component modules.
- `proof/progress/`: a dependency-closed checked progress checkpoint covering literal 326, global elliptic generation, actual heights, local logarithms and source bridges.
- `checks/`: independent coefficient, transformation, and sum-of-squares checks.
- `tools/`: compiler, exact sparse arithmetic, and generation command.
- `docs/`: [arithmetic derivations](docs/arithmetic.md) and pinned source manuscripts.

## Proof status

[`polynomial_zero_iff_source`](proof/318/Current318FinalBridge.lean) proves equivalence between zeros of the 318 polynomial and witnesses of its 288-equation source. [`degree_exactly_four`](proof/318/Current318FinalExactDegree.lean) proves its degree. The original integer-characterization theorem still assumes `sourceArithmetic`; the complete global arithmetic argument is not yet formalized.

The [checked progress checkpoint](proof/progress/README.md) now also proves the literal 326 source/lift/coefficient-table connection, unconditional global elliptic generation and raw source labels, actual canonical-height bounds, and the odd-index product-height identity. The complete local/analytic soundness joins now prove that zeros of either published polynomial have integer input conditional only on the explicitly named `FiveContact49Height` geometric theorem. Exact Lucas growth and positive odd Lucas witnesses are also checked. The latest checkpoint adds actual finite normal affine models, their height-one Spec stalks and faithful-flat DVR completions, and compatible quadratic normalization under completion. It also constructs the actual smooth relative-dimension-one Weierstrass scheme from affine/infinity charts, exact base changes and field-valued points, Kähler frames, and the complex Gamma1 quotient atlas and differential vector bundle. Earlier checkpoints contain all-branch complex-torus uniformization, torsion transport, invariant/torsor descent, and actual section extension/sheaf gluing. Earlier cusp/Wronskian, local-different, branch/projective, q-series and metric producers feed a checked assembly from explicit `GeometricRealization` data to the five-contact theorem and both polynomial endpoints. That geometric data existence is not yet constructed in Lean, and the witness-existence direction remains separate. Source-level geometric reviews and record projections are not treated as the final theorem.

The written argument combines reciprocal elliptic charts, the odd-input bridge, three-helper pole normalization, valuation norm chains, and the 49/8 height bound. [Arithmetic derivations](docs/arithmetic.md) supplies the details; [remaining Lean obligations](proof/components/arithmetic-obligations.md) identifies the formalization gap.

## Generate

Python 3.11+ and Node.js 24, with no third-party runtime packages:

```sh
python tools/generate.py
```

Outputs go to `build/results/`; use `--output PATH` to choose another directory.
To compare generated coefficients with the published tables, run `python tools/generate.py --check`.

Focused checks are available in `checks/` for coefficient expansion, affine inverses, and the unique lift. Run unit tests with `python -m unittest discover -s tests`.

## Build the Lean proofs

The Lean packages pin Lean 4.35.0 and Mathlib. With that toolchain installed:

```sh
python tools/unpack_data.py
cd proof/318
lake exe cache get Mathlib.Tactic Mathlib.Data.Rat.Lemmas Mathlib.Algebra.MvPolynomial.Degrees Mathlib.Algebra.MvPolynomial.NoZeroDivisors
bash verify_concrete.sh
cd ../components
lake exe cache get
bash verify_components.sh
cd ..
bash verify_all.sh
```

The scripts enable kernel checking and audit theorem dependencies against `propext`, `Classical.choice`, and `Quot.sound`. [Build receipts](proof/receipts/) retain the original runs. A [fresh rebuild](proof/receipts/fresh-rebuild/receipt.json) kernel-checked all 18 concrete modules and 50 component modules, audited all 1,968 and 881 declarations respectively, and checked the seven new constant-lift theorems. The official Lean binary and pinned Mathlib cache were trusted inputs, not rebuilt. `proof/verify_all.sh` repeats the selected and full-declaration audits and the new helper check.

## Sources

Based on [José Brox’s v3 manuscript](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/f4d1b5e6c23d4adeb3ae1f986ab0bf87884bdff6/paper/diophantine_optimization_20261106_v3.tex) and [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q/tree/ba7a3e0a0c171b7cd2ce75976addba57fad8a5dd), including Gabriel Conant’s odd-product and asymmetric-depth construction. The pinned manuscripts are in [`docs/sources/`](docs/sources/). Upstream attribution and applicable licenses remain with their authors.

## Historical Lean generators

The `generate_*_general.py` scripts retain their frozen historical paths and are not the current package regeneration interface. Use `tools/generate.py` from the package root for the published coefficient tables; the checked Lean sources are supplied directly. Run `python tools/unpack_data.py` from the package root before the Lean commands above.
