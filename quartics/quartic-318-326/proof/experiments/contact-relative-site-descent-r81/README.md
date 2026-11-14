# contact-relative-site-descent-r81

Draft successor to `contact-relative-site-descent-r80` at `d97d209a1666cdcb0d7ae2488523fbfa7d46fae6`.

## Exact hosted evidence

Run 43575728180, job 132389976178, artifact 14106378665. The direct stderr positive control and command markers00 through04 appear, ending after original_overlap_of_object_eq. Marker05 after reconstructed_actual_overlap is absent. The module timed out124 after180.071 seconds. This identifies an observed command frontier, not completion of earlier asynchronous work.

## Bounded repair

Diagnostic-only successor: insert two direct flushed run_tac IO markers at entry and exit of reconstructed_actual_overlap around its unchanged sole exact expression. Existing ten command markers, statements, mathematical proof expression, imports, options and budgets are unchanged. Removing the two recorded insertions restores every predecessor byte. Native run_tac/TacticM and IO lifting APIs are pinned to Lean v4.35.0.

## Scope and verification

287 root modules in the original order; 1 changed and 286 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The new markers distinguish observed tactic-body progress from command-frontier progress only. Entry absent may reflect statement/type work or other earlier async activity; entry present with exit absent may implicate nested term elaboration but does not isolate a conversion. Exit present still does not certify kernel/asynchronous completion, and no timeout fix or module pass is claimed.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
