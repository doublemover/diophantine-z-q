# Literal 326 polynomial replay: completed

All four targeted finite-algebra obligations now have kernel-checked Lean proofs. The global arithmetic premise remains open. These were gaps in the supplied formalization, not findings that the written mathematical arguments were false or historically absent.

## What is proved

1. **Literal residuals and SOS semantics.** `Current326Polynomial.lean` encodes the 326 coordinates, 296 quadratic residuals and 1,263 residual terms. `zero_iff_constraints` proves that the rational SOS vanishes exactly when every residual vanishes. The input is coordinate zero, leaving 325 existential witness coordinates. Every parameter power in the literal residual data is zero.
2. **Unique lift and exact 326-to-318 equivalence.** `Current326Bridge.lean` checks all 288 inherited rows, including the three changed rows 275, 277 and 287, and the eight new chain/product rows. It accounts for the compiler's sign flips. `unique_lift` proves that every lifted solution is the canonical eight-coordinate extension of its first 318 coordinates. `polynomial_zero_iff_318` proves equality of input projections. The original input coordinate is preserved.
3. **Exact degree four.** `Current326ExactDegree.degree_exactly_four` uses the unchanged isolated square gate at row 153, whose square coordinate is 40 and output coordinate is 192.
4. **Exact stored coefficient-table equality.** All 296 row squares are expanded by Lean into 4,128 sparse contributions. A transparent normalization algorithm has a generic proof that it preserves polynomial interpretation. Lean's kernel then checks that the normalized data equal the literal 3,157-term table. `Current326CoefficientBinding.table_eq_sos` identifies the table polynomial with the SOS polynomial. This is not a Python-only convolution check.

The public end-to-end interface is `Current326Final.lean`:

- `stored_term_count`: the literal table has 3,157 entries.
- `table_degree_exactly_four`: the table polynomial has total degree exactly four.
- `table_zero_iff_318`: its 325-witness input projection equals the 318-coordinate polynomial's 317-witness projection.
- `table_zero_iff_source`: its zero set is equivalent to the original raw source system.
- `defines_integers_of_source_arithmetic`: the integer characterization follows only if the explicit global source-arithmetic premise is supplied.

## Verification and trust boundary

- All **2,021 declarations in nine new modules**, including private and generated declarations, passed the recursive axiom audit.
- Only `propext`, `Classical.choice`, and `Quot.sound` were allowed. No custom axiom or `sorryAx` was accepted.
- All new modules were compiled with `-Ddebug.skipKernelTC=false`.
- The finite normalization uses `decide +kernel`, not native execution or `native_decide`.
- A separate strict parser verifies every residual term and every coefficient-table entry against the supplied JSON, including coordinate bounds, the 50 table chunks and their exact order. File serialization and SHA-256 checks are external checks; Lean certifies the algebra on the encoded data.
- The 45 frozen 318 source/input hashes are unchanged.
- No `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide` occurs in the nine proof modules.
- Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned. The official Lean binary and upstream Mathlib cache remain trusted inputs; this is not an independent rebuild of Lean or Mathlib.
- No repository file was edited, and no PR was created.

## What remains open

The raw source's arithmetic characterization is still an explicit theorem parameter. This finite replay does not prove concrete elliptic-curve arithmetic, local-place realization, formal logarithm comparisons, global height/separation estimates, or rational-witness completeness. A clean axiom audit does not discharge a theorem parameter.

## Reproduce

Use the pinned Lean toolchain and populate the dependencies/cache recorded by `lake-manifest.json` without changing the frozen manifest. From the extracted directory, run:

```
bash verify_literal326.sh
```

The script checks hashes, rebuilds the frozen 318 dependencies, checks the generated-data binding, kernel-checks the nine new modules, and runs the recursive axiom audit. `literal326-verification.json` records the successful module commands, source/log hashes, exact scope and remaining premise. `Current326FullAudit.lean` is the all-declarations audit; `check_literal_data_binding.py` is the separate serialization check.
