# 318- and 326-variable quartics

This branch adds a contribution package alongside the existing Version 10 construction. It does not replace or revise the published manuscript, historical inventories, or accepted Lean snapshot.

| Construction | Total variables | Witnesses | Degree | Monomials | Largest absolute coefficient |
| --- | ---: | ---: | ---: | ---: | --- |
| 318 | 318 | 317 | 4 | 3,134 | `64 * 3^(2^17)` |
| 326 | 326 | 325 | 4 | 3,157 | `3^2048 + 3813373282171 < 2^3247` |

Both tables include the input as coordinate zero. The 318 table specifies the fixed integer `S=3^(2^16)`, and also supplies complete decimal exports. The 326 construction replaces that constant by eight uniquely determined additional coordinates to reduce the coefficient height.

## Files and argument

- [Contribution package](../../quartics/quartic-318-326/README.md), [counts and hashes](../../quartics/quartic-318-326/results/manifest.json).
- 318: [exact symbolic table](../../quartics/quartic-318-326/results/318/polynomial.json), [complete decimal text](../../quartics/quartic-318-326/results/318/coefficients.txt).
- 326: [complete decimal text](../../quartics/quartic-318-326/results/326/coefficients.txt), [JSON table](../../quartics/quartic-318-326/results/326/polynomial.json).
- [Written arithmetic derivations](../../quartics/quartic-318-326/docs/arithmetic.md) and [source construction](../../quartics/quartic-318-326/construction/318/build_source.cjs).
- [Lean polynomial/source equivalence and degree](../../quartics/quartic-318-326/proof/318/README.md), [arithmetic helper modules](../../quartics/quartic-318-326/proof/components/README.md).

## Reproduce

From the repository root, with Python 3.11+ and Node.js 24:

```sh
python -B scripts/check_quartic318_326.py
```

This runs generation and byte comparison of both coefficient tables, all independent finite checks, unit tests, and the frozen Lean source/input hash checks. Generated inputs and logs stay under `build/quartic-318-326/`. No third-party Python packages are needed. For a Lean rebuild with Lean 4.35.0 and the pinned Mathlib dependencies, follow the package instructions. The finite runner does not run Lean.

## Verification and provenance

The Lean bridge proves equivalence between the exact 318 polynomial and its quadratic source system, and exact degree four. The integer-characterization theorem still assumes `sourceArithmetic`; the global arithmetic argument is not fully formalized. The 326 lift is checked with exact Python arithmetic. The written argument depends on the inherited arithmetic inputs documented in the package. Passing finite checks is not a proof of those inputs or a claim of independent human peer review.

This contribution was developed with OpenAI coding assistants. It builds on José Brox’s pinned v3 manuscript, the Version 10 manuscript, and Gabriel Conant’s odd-product and asymmetric-depth construction. Source attribution remains in the package. Historical Lean rebuild receipts are retained as historical evidence, not presented as new integration runs. [Integration provenance](../../quartics/quartic-318-326/INTEGRATION.json) records the upstream base and payload identity.

The package keeps its internally referenced directory structure. Shared Lean modules and proof inputs use relative links, avoiding repeated copies; coefficient tables are linked directly rather than duplicated as top-level downloads.
