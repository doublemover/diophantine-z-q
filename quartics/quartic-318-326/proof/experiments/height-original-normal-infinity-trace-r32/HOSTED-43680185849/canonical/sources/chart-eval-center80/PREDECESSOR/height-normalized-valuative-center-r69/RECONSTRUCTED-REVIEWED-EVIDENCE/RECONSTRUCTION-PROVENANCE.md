# Explicit hash-verified reconstruction, not retained originals

The exact reviewed HOSTED_REPAIR.json and SOURCE_VALIDATION.json byte sequences were not located in the final owner tree, local reviewed snapshots, current geometry archive, or inspected PEL recovery archives. Library read with version_id 0 returned the current version-1 content identifier/size; a version-scoped search yielded no historical file. No Library version was restored or mutated. These observations do not prove historical storage lacks the old bytes.

The original builder records propagation_review as PENDING. The finalizer replaced that existing value with PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING; it did not add a previously absent key. The included script copies and pins the unchanged current receipts, then reverses only that value using the original JSON indent-2/newline serialization. Each resulting SHA256 must equal the independent, pre-existing reviewed APPLICATION binding. Reapplying the status value must reproduce the current input bytes exactly.

RECONSTRUCTED-REVIEWED-* files are explicitly reconstructed byte-equivalent snapshots, not retrieved/retained originals. Current source, intake, README, HOSTED_REPAIR.json and SOURCE_VALIDATION.json are unchanged. No claim of Lean or kernel acceptance changes. Independent narrow metadata addendum is required before refreeze.
