# Norm descent product parser repair

Fresh strict run43998697646 rejected the unspaced intended product |b|*|c| because the parser recognized the unintended |* token. Add exactly two ASCII spaces, yielding |b| * |c|. All arithmetic proof steps, hypotheses, imports, options and resource limits remain byte-identical. The intended product bound is preserved; the old malformed declaration did not have an accepted kernel signature to compare.

All1345 other sources and the1346-root order are unchanged, including strict-accepted JacobiProduct, CRT, normalization and common-value sources. The replay remains the same native-only norm-descent root. No full ternary induction or additional mathematical layer is included. Source/API review is not Lean acceptance; strict checking remains required.
