# Independent scalar-contact and final source join review

PASS. Four exact copied modules were rebuilt with Lean 4.35.0 and `debug.skipKernelTC=false`. Recursive axiom collection passed for all 56 declarations belonging to those modules, with only propext, Classical.choice and Quot.sound. Copy hashes were compared again to the author files after completion and agree. This is a fresh rebuild of the four named modules, not a fresh rebuild of every imported dependency.

## Mathematical checks

- The actual scalar beta is 3723(2w0+1)^2. Away from 3,17,73 its valuation is even. Coprime reduced numerator and denominator then separately have even valuations, so the odd-contact radical has no zero or infinity contributions. The beta=0 case is handled by its zero height, not by evaluating an omitted-contact theorem at a prohibited point.
- The three remaining primitive forms map to the actual contacts 1,2401,-343/32. The scalar polynomial has the additional root 1/2; every pairwise root difference has support in 2,3,5,7,359,4801. Those primes really occur in the excluded set. The selected contact is therefore the unique positive-valuation factor, with the same positive odd depth in the literal source r.
- The scalar wrapper invokes the actual split/inert p^8 index theorem for the same coherent Labels witness. It derives h(beta) <= H |c|^(49/64), retaining only the explicitly named FiveContact49Height geometric statement.
- The high target is exactly N2^2 - N1(N1-2)N2 N3 + (N1-2)^2 N3^2 - 1. Its real cast agrees with the numerical Lucas residual. The three detector comparisons all use the same global root labels, and their nonzero target branch is explicit.
- The optimized low beta coordinate is not assumed definitionally equal to the polynomial: literal source residual r79 proves the identity. The reduced-numerator target, absolute-value cast, and nonzero branch are then correct.
- The final source_integer_input chooses one unconditional Labels witness, obtains the scalar nonzero/anchor/orientation and odd-root bounds, and applies the already checked three-height numerical separation theorem. There is no newly retained label, group, local-place, logarithm, or numerical-height premise.

## Exact conclusion and boundary

`SourceHeightComparisons318.source_integer_input` proves that literal Constraints(stage0(3^65536)) imply w0 is an integer, **conditional on ContactHeight318.FiveContact49Height**. The recursive axiom audit does not prove this proposition: it remains an explicit argument. This review does not establish the geometric five-contact theorem or unconditional sourceArithmetic, nor any completeness statement.

Reproduce with `bash soundness-local/source-join-review/review.sh` from the workspace. Source hashes and the verified log are recorded in receipt.json and REVIEWED_SHA256SUMS.
