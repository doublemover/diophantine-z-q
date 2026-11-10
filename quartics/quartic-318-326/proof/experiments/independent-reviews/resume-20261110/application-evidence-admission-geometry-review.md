# Independent review: declared application evidence admission

Reviewer: resume_pel_geometry. Author: reconcile_review_queue. Date: 2026-11-10.
Bound files:
- scripts/check_progress_experiment.py SHA256 11ece0903b153bc7f91ad99038f2fa9e1fe23ef37730deab5ab2be03893a045d
- scripts/test_progress_experiment.py SHA256 e8e9e0a9c25c8507602f172c57d031d4a9691d94ecf45f76d95c555c4989013a

Verdict: CLEAR. Read the complete small diff. Admission now checks declared APPLICATION.bindings before accepting intake. It validates mapping shape, string paths, exact lowercase SHA256 syntax, file presence, and exact bytes. Resolved path containment rejects both parent traversal and symlink escape before reading evidence content. Legacy/tooling fixtures with no APPLICATION and packets without declared bindings retain existing behavior; this is an explicit declared-binding check, not a mathematical contract validator.

Reran all 12 tests successfully. Independently tested an in-packet symlink to an outside evidence file and confirmed Invalid application evidence binding rejection. Existing missing/stale/path/digest/type negative controls pass. No Lean source, budget, audit semantics or theorem acceptance criterion changes. No local Lean was run.
