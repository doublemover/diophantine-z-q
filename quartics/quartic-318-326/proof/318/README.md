# Concrete Lean verification: 318-variable quartic

This frozen artifact proves the entire algebraic circuit-to-polynomial statement for the supplied 318-coordinate polynomial.

## Checked result

`Current318FinalBridge.polynomial_zero_iff_source` proves that, for every rational input q, the literal integer-coefficient polynomial has 317 rational witnesses exactly when the supplied raw 318-coordinate, 288-equation source has witnesses with that same input. The replay includes the affine anchor translation, every recorded normalization and elimination, and the final compact-coordinate map.

`Current318FinalExactDegree.degree_exactly_four` proves that the polynomial has exact total degree four. All 288 quadratic residuals occur literally in `Current318FinalPolynomial.lean`; the polynomial is the sum of all their squares. The fixed integer S = 3^(2^16) is a coefficient, not an extra variable.

## Arithmetic interface

`Current318FinalBridge.defines_integers_of_source_arithmetic` assumes the displayed source characterization: for every rational q, the raw source has rational witnesses if and only if q is an integer. The global arithmetic characterization is an explicit theorem parameter, not a custom axiom.

The expanded coefficient table, coefficient height and monomial census accompany the independent finite-check metadata.

## Reproduce

Use the official toolchain in `lean-toolchain` and the exact dependencies in `lake-manifest.json`. In a fresh copy, obtain the pinned official Mathlib cache, then run:

    lake exe cache get Mathlib.Tactic Mathlib.Data.Rat.Lemmas Mathlib.Algebra.MvPolynomial.Degrees Mathlib.Algebra.MvPolynomial.NoZeroDivisors
    bash verify_concrete.sh

The script verifies frozen hashes, rebuilds every local proof module with kernel checking enabled, and rejects dependencies outside the standard Lean axioms propext, Classical.choice and Quot.sound. No proof holes or custom axioms occur. Every emitted identity is proved by Lean’s checked ring procedure.

`Raw318FinalReplayMonolithic.lean` preserves the generated replay in a single file. Split modules make rebuilding practical. `concrete-verification.json` states the exact boundary and records all hashes.

## Historical generators

The `generate_*_general.py` scripts retain their frozen historical paths and are not the current package regeneration interface. Use `tools/generate.py` from the package root for the published coefficient tables; the checked Lean sources are supplied directly. Run `python tools/unpack_data.py` from the package root before the Lean commands above.
