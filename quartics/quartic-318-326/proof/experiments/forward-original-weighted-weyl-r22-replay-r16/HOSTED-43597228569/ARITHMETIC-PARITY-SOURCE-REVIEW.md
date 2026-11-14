# Independent small-prime parity source and current human-contract review

Verdict: source-level approval of the single bounded repair for hosted replay, not a claim that the module timeout is resolved. Reviewed candidate `ScalarSmallPrimePreparation318.lean` SHA256 `e808d212ea6cd4edc8fe7ca8b839b19b80480adfacddf0671d227ce6ee8bec9e`, before `bf67a3951d82a74007d19237aa86334078f07aee2c6f20caafa434a6ae3d034b`, and current `FORWARD_APPLICATION.md` SHA256 `96d5e9b24703878cab5c009b0d65875c72f73cb01a7714cf80322495018ec1ab`.

## Authentic observation and exact delta

Independently verified both own official artifact ZIP digests, embedded files, run 43597228569/head 2af419e128047c483b3cdc0ba5e4d65c09d7c4ce, published intake and before-source bytes. Ordinary descent and weighted results stop at this module with exit124; the ordinary wall-limit log does not localize the failure.

The separately nonadmitted descent diagnostic contains exact cumulative source prefixes. Prefix0 exits0; prefixes1/2 exit1 at 2.139/2.213 seconds with unknown `Int.pow_emod` and the remaining modulo-two goals. Prefixes3/4/5 hit their 2MiB **log caps**, not their 90-second wall caps, at 34.251/34.596/34.905 seconds. Those trace-heavy outcomes are not proof of a particular kernel phase or of a new Lean error. The source-different historical r14 control hits its 90-second wall cap. All scratch nonadmission fields remain false for acceptance.

The whole-file inverse check proves the only source edit is replacing `Int.pow_emod` in the one parity simp list by `pow_two, Int.mul_emod`. The independently Git-blob-verified native Lean source at compiler eb6cafb7290e8bd5f2937522d8d804f58f02bafc supplies the exact multiplication-modulo identity. Expanding the square and using that identity applies to the existing exhaustive `x % 2 = 0` or `1` branches, with no extra parity assumption. Parsing, simplifier termination and kernel checking still require hosted execution.

## Mathematical and consumer boundaries

The variable remains every integer a and x remains a+a². The theorem's three literal114444 multiplier factorizations, all integer witness polynomials and all coefficients are unchanged. The proof still derives the needed integer j from divisibility of x+x², and the original 2-adic equality still uses64*hj. No branch, prime2/3/17 case, exceptional input or mathematical statement is removed.

The same-module `actual_multiplier_values` is untouched, including its actual rational cast and values4/2/2. Its potentially expensive unit/valuation/convert proof is not represented as fixed by this patch. The unchanged values feed `actual_pole_thresholds` and `actual_preparation` at the same assignment w, integer n, integer input a and original scalar `poleInput w n`. All original nonzero and local preparation hypotheses remain; none is supplied as a new premise to the changed lemma.

Read the exact pinned consumer copies: PreparedTwistSource applies actual_preparation; PreparedLucasSource applies actual_multiplier_values and actual_pole_thresholds; AllScalarSupportPreparation applies actual_pole_thresholds. The human contract correctly distinguishes these consumers from a mere importing module. The existing maxHeartbeats0 option, imports, all public telescopes, all later proof text, full intended1299/1304 closures and all resource/trust settings are unchanged by this source delta.

## Review boundary

`check_arithmetic_parity.py` passed independent static identity, one-edit, native API provenance, artifact, diagnostic and producer/consumer checks. No local Lean, Lake, compiler or proof evaluation ran. This is source and current human-contract review only: future packaged machine obligations, exact-copy propagation and final staged-tree review are separate. No new candidate hosted pass, recursive axiom audit, full packet acceptance or timeout resolution is claimed. The later targeted diagnostic is not included in this approval.
