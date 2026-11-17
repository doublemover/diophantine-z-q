# Norm descent less-than parser repair

Fresh strict run43995107772 rejected the unspaced intended inequality |c|<|b| because the parser interpreted <| as function application. Add exactly two ASCII spaces, yielding |c| < |b|. All proof bodies, hypotheses, imports, options and resource limits remain byte-identical. The intended inequality is preserved; the old malformed declaration did not have an accepted kernel signature to compare.

All1343 other sources and the1344-root order are unchanged, including strict-accepted JacobiProduct, CRT, normalization and common-value sources. The replay remains the same native-only norm-descent root. No full ternary induction or additional mathematical layer is included. Source/API review is not Lean acceptance; strict checking remains required.
