# Initial cold failures and actual hosted warm-cache validation

Head: 8d7ca58063f1825f99bf350f4115f22b1245a7bd. This is a targeted diagnosis, not a full-cohort acceptance or a routine monitoring report.

Finite run 42467270104 job 128689578271 and research run 42467270053 jobs 128689578091, 128689578163, and 128689578305 all failed before project checks. Each correctly attempted the exact new Python runtime cache first, saw an initial cold miss at approximately 09:27:52 UTC, then received three HTTP 504 responses from the unchanged official Python 3.12.14 Linux 24.04 archive. No setup validation, Lean proof, project test, or cache admission defect is established by these failures. Research Windows V9 was cancelled by the matrix after the Linux failure, not independently diagnosed as a Python failure.

The exact same branch-scoped Python cache was successfully created at 09:28:14.885734 UTC, after those first restore attempts. The API records cache ID 10187601158, 79,345,965 bytes. A successful sibling also cold-installed and verified Python after an initial 504, confirming transient upstream behavior rather than a permanent invalid version or URL.

Actual subsequent foundation job 128689984623 in cohort run 42467270037 hit this exact Python cache at 09:29:41.659, restored it by 09:29:43.046, and setup-python recognized and verified CPython 3.12.14 without downloading Python. This same job restored the exact elan archive and Lean release cache, verified the archive SHA and exact Lean 4.35.0 commit, and reported Lake 5.0.0. The Lean runtime archive restored in about nine seconds. No toolchain download was needed. The separate project whole-snapshot and cohort caches also restored; their admission remains the existing byte/dependency audit, not this tooling observation.

The planner log separately records a successful Python cold install after two 504 responses, followed by actual warm elan and Lean restoration and exact version verification. This validates the intended cold-to-warm path, while preserving the first-cold-fetch network limitation.

Recommended action: retry only failed jobs of the finite/research runs using the now-published exact cache. No source or pin patch is justified by these logs. A new cache key, eviction, inaccessible cache scope, or transport outage can still require a cold official download. A finite number of retries cannot guarantee service during an upstream outage. Cross-workflow jobs starting simultaneously before the first save can all see a cold miss; this was already an explicit audit limitation.

No rerun is performed by this receipt. Parent coordinates retries and monitors the remaining cohort. Combined 1,386-module validation is not claimed. Analytic packet outcomes are handled in their own exact mathematical receipts.
