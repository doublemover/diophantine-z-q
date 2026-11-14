# contact-relative-site-descent-r83

Draft successor to `contact-relative-site-descent-r82` at `6fe85071934d36d22cfdbd7c503f6b9a54e6ef18`.

## Exact hosted evidence

Run 43582938856, job 132411887362, artifact 14109024226. The module timed out124 at 180.131 seconds. Native helper profiler rows appear, including exact tactic 4.68 seconds, and both body markers appear; command05 is absent. The separate profiler control BEGIN/timing/END are all absent. This is not a successful positive control and does not isolate the post-body/kernel/async phase.

## Bounded repair

Diagnostic-only one-line API correction: replace the unsupported Options.setNat call in the no-op profiler control with native Options.set and explicit (0 : Nat). Pinned Options.lean defines generic set/setBool, not setNat; pinned KVMap defines Value Nat. Every proof, statement, control action, flush, marker and scoped profiler option otherwise remains byte-identical. This corrects an option-setter check missed by the earlier source review; that review did not establish control elaboration.

## Scope and verification

287 root modules in the original order; 1 changed and 286 unchanged. No modules added or deleted. No source options, imports, resource/async/trust settings or module boundaries change. Existing helper-scoped profiler true/threshold1 and stderrAsMessages false remain. Only the diagnostic control builds the same threshold0 Options through the supported typed setter. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

A control elaboration failure is consistent with its absent BEGIN/END because the whole command elaborates before execution, but the timeout log contains no rendered control error, so its precise runtime failure is not claimed proven. Corrected control compilation/output still needs hosted checking. Native timings report only completed regions and can be buffered; neither body-exit nor a timing row establishes declaration/kernel/earlier async completion.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
