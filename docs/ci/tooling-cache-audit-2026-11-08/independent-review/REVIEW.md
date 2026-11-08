# Independent CI and cache source review

## Status and independence

This review accepts the bounded tooling changes with the exact final file hashes
in SOURCE-BINDINGS.json, based on repository head
`a54ba7cc1a534589d04b4b19afd060389aedacde`. No blocking issue remains within
that stated scope. Actual hosted validation remains pending. The reviewer did
not edit shared sources, run a Lean compiler, replay the proof chain, or dispatch
a workflow. The coordinator authors and tests the patch. The reviewer supplied
specific findings and inspected the resulting fixes, so this is an independent
source review with disclosed design feedback, not independent authorship of the
entire CI system. Prior bounded reviews of experiment admission are retained.

All six workflows, four runtime composite actions, the runtime installer, the
bundle-layout normalizer, both progress checkers, accepted-helper checker,
manifest admission, current private-inclusive audit body, and relevant tests
were read. The reviewer also read actual pinned upstream setup/cache/artifact
implementations. `UPSTREAM-SOURCES.json` records verified locators and Git blob
hashes. This is not a penetration test, audit of repository administration or
branch protections, rebuild of upstream actions, or mathematical proof review.

## Concrete findings and repairs

1. **Optional runtime cache transport was initially fatal.** At the pinned
   actions/cache implementation, restore exceptions mark the step failed.
   Consequently an outage could stop a job before its normal runtime installer.
   The revised composites allow only cache restore transport to fail, then still
   run the existing installer and fatal exact-version/checksum checks. Save keys
   are explicit rather than depending on restore outputs that may be absent.
   A corrupt cached installer remains a fatal integrity failure. This distinction
   does not allow a failed compiler or proof check to become a success.

2. **New tooling tests initially had triggers but no execution step.** The
   existing `test_*lean*.py` discovery does not include `test_ci_tooling.py`.
   The coordinator added explicit invocations to both progress plan jobs and
   research construction. The final binding includes those calls and tests.

3. **Singleton artifact layout did not match the verifier.** The actual pinned
   download-artifact v8 source extracts a one-match pattern directly to the
   requested root. `collect_bundles` expects a `progress-cohort-ID` subdirectory.
   The documented manual `cohorts=1` option could therefore fail at the first
   cross-stage download. Default 16-cohort runs are not thereby invalidated.
   The new normalizer moves the exact flattened bytes under the receipt's
   nonnegative integer cohort ID, rejects failed or mixed layouts, and changes
   no proof admission. All three download sites call it before the unchanged
   verifier. Negative controls cover failed status, path-like and Boolean IDs,
   and mixed layouts; successful singleton and already-nested cases are covered.

4. **Accepted-progress source lint was weaker than experiment admission.** The
   original verifier rejected placeholders/native evaluation but did not ban
   source-level kernel overrides, unsafe declarations, implementation overrides,
   or new axiom declarations. A fresh read/scan of all 1,386 current modules found
   no such occurrences. This finding concerns future admission, not an observed
   invalid current theorem. The revised verifier uses the existing comment/string
   parser, checks the audit source too, rejects optimized Python, and distinguishes
   bare unproved constant declarations from legitimate `constant` field/definition
   names. Negative and positive controls and the documented progress-directory
   entrypoint are tested. It is now explicitly repository-scoped because it
   imports the existing parser from the resolved repository scripts directory.
   The parser/checkers and actual proof source bytes remain unchanged, so current
   artifact keys need not be invalidated: stricter admission runs before reuse.

5. **Runtime downloads were repeated despite unrelated caches.** A TeX bundle
   cache does not cache the Tectonic engine archive; dependency caches likewise
   do not preserve Python or Node runtimes. The new caches store the exact Python
   version directory including completion marker, exact Node version directory,
   SHA-checked elan archive, one selected Lean release directory, and only the
   SHA-checked Tectonic archive. They do not store the entire home directory,
   Mathlib trees, project outputs, npm caches, or experimental artifacts.

6. **Retry evidence and retention needed clearer boundaries.** Successful cohort
   bundles retain stable verifier-consumable names; failed logs receive a separate
   attempt-qualified namespace excluded by the successful-bundle download pattern.
   Seven-day retention replaces the two-day outage retry window. This is evidence
   hygiene and retry resilience, not a claim that every same-name rerun previously
   failed with HTTP 409. The locked artifact SDK explicitly lists reruns as a
   duplicate-name case; the pinned downloader requests latest and the SDK retains
   the highest artifact ID per name. It still undergoes our exact snapshot and
   byte verification. The review does not claim to have exercised GitHub's hosted
   rerun backend dynamically.

## Runtime paths and retained trust

Python and Node use exact numeric versions and `check-latest: false`. Their actual
pinned action implementations try the installed tool cache before remote version
lookup/download on this path. Keys separate OS, architecture, runner image and
version. Python setup still supplies its normal PATH/library-path environment;
the restored directory is not executed through a substitute project interpreter.
Node's package-manager auto-cache is explicitly disabled.

Elan is downloaded to a temporary partial filename, verified against the existing
full SHA256, then renamed and cached. Cached bytes are reverified before extraction.
The installation does not rewrite shell profiles or choose an unrequested default
toolchain. Both project Lean pins must remain exactly 4.35.0. The chosen runtime is
checked against the existing version and commit identifier. This is the repository's
existing trusted compiler-release model, not an independent checksum proof for all
compiler executables. Only that one toolchain directory is cached, before Mathlib
downloads. It is not a combined multi-gigabyte toolchain/dependency/project cache.

Tectonic calls the existing `build_paper.install()`, which verifies the pinned
archive SHA on every call and extracts only the expected executable. The ordinary
paper build continues to check the exact engine version, selected TeX bundle
fingerprint, errors/references, unchanged manuscript bytes, and resulting PDF.
The engine cache does not bypass the bundle or paper checks. Existing untrusted-TeX
mode remains enabled. The optional rendering package installation is used only
when the needed utilities are absent.

Caches are trusted repository CI accelerators, not independently verified proof
certificates. GitHub branch/ref scoping and repository write access remain part
of that trust boundary. Version output checks cannot independently authenticate
a maliciously replaced interpreter that lies about its version. This patch does
not claim to change that general trust model or to certify repository permissions.

## Proof-cache admission and invalidation

The unchanged progress checker binds each module to its source hash, recursive
project-import keys, compiler flags, toolchain pin, upstream manifest, checker and
parser. Reuse additionally requires the actual already-selected dependency artifact
hashes and exact stored bytes for each artifact suffix. A changed dependency
invalidates dependents; unrelated modules may be reused. Prefix fallback to an
older full snapshot is not an unconditional reuse decision.

Each cohort builds into a new isolated library path, and inherited project library
paths are replaced. Upstream package revisions and tracked source cleanliness are
checked. Missing pinned upstream artifacts can be compiled from pinned sources.
Previously completed stages enter only through exact PASS receipts, expected
cohort/snapshot keys, exact module coverage and dependency-artifact comparisons.
Inconsistent duplicate module bytes are rejected. Only fully completed cohort
outputs are saved. A failed cohort is not a successful full snapshot.

The final merge checks complete coverage and consistent compiler identity, then
always reruns the actual private-inclusive recursive axiom audit across the full
snapshot. Its allowed roots remain propext, Classical.choice and Quot.sound.
Only that successful merge creates the full-baseline cache. Clean mode rejects
project artifact reuse in both producer and consumer receipts. It still trusts
the selected compiler and upstream artifacts as documented.

Experiment admission remains separate: exact source hashes and import records,
reserved/baseline module shadow rejection, explicit source safeguards, only the
needed verified predecessor closure, fresh output tree, bounded strict compiles,
and its own private-inclusive new-module audit. No experimental proof artifacts
are saved in the accepted cache. A successful experiment is not source acceptance
or mathematical completion. Empty packet matrices skip checking deliberately.

The reviewer freshly confirmed that all 1,386 accepted source hashes match their
manifest and that `check_progress_lean.py`, `check_progress_experiment.py` and
`check_lean.py` remain unchanged relative to the stated base head. These checks
are not a new compilation or full hosted PASS claim.

## Six-workflow coverage

- **Progress Lean cohorts:** all three dependency stages and complete audit were
  traced. Empty later stages are explicitly gated. The current main workflow does
  not cancel a running full replay. It does not promise to replay every intermediate
  commit: GitHub concurrency keeps only its permitted pending run. Manual clean,
  cohort and boundary controls remain checked by the planner.
- **Progress Lean experiments:** a plan validates named packets, gates an empty
  matrix and warms tooling before fan-out. Only exact older-baseline artifacts
  satisfying the required closure are eligible. Latest relevant pushes can cancel
  older experimental runs; a canceled run is not a PASS. Result/log uploads remain
  distinct from promotion.
- **Research checks:** Linux/Windows finite and historical reconstructions, current
  paper, source inventory and all 48 accepted Lean helpers remain separate jobs.
  The helper checker creates fresh project outputs and audits all 48 modules; it
  does not count the quarantined final target as proved. Shared runtime setup does
  not replace these checks. Latest-run cancellation remains intentional.
- **Check 318/326 quartics:** the finite checker remains a finite construction and
  source-binding check. It is not the full Lean cohort replay or unconditional
  arithmetic theorem. Exact runtime substitutions do not change that scope.
- **Manuscript integration:** the explicit manual mode gates retain reproduction,
  paper and metadata coverage. Current Version13 and historical versions remain
  distinguished. Windows uses its separately pinned Python version. Paper rendering
  is a visual-review artifact, not mathematical proof acceptance.
- **Version5 handoff release:** manual-only and restricted to the original named
  repository, with write permission isolated to that workflow. It verifies the
  unchanged historical archive, packaging and extracted replay before draft-release
  creation, and refuses an existing tag/release. It is not an active release path
  for the current doublemover fork. No release was created by this review.

## Residual operational limits

- Warm-up attempts to save caches before matrix jobs, but the pinned save action
  may warn and finish without a successful upload. A green warm-up is not proof
  that every following job will hit the cache. Fork cache permissions, retention,
  eviction and repository quota can also cause misses.
- Cold downloads, upstream Mathlib cache, GitHub artifact transport, TeX bundle,
  and occasional rendering-package fetches remain network dependencies. The fix
  improves warm reuse; it does not make a first cold outage disappear or loosen
  checks to work around it.
- The three progress download joins are explicitly normalized; missing/expired
  or incompatible bundles still fail closed. After retention expires, retrying
  only a late failed job may require rebuilding earlier producers or a new run.
- Default GitHub hosted disk/cache quotas and actual warm transfer time were not
  measured in this read-only review. The new compiler-only cache avoids the known
  combined-tree design, but real cold/warm workflow evidence is still required.
- Current upstream fetching includes more than an individual experiment's minimal
  dependency closure. This is a performance opportunity, not an admission flaw;
  changing the verifier for it would deserve separate source-bound review.
- Static/mocked regressions and pinned-source inspection do not replace the next
  actual hosted runs on Linux and Windows. No result below should be described as
  a successful hosted proof replay until those actual result artifacts exist.

## Validation evidence read

The reviewer read the coordinator's durable local logs: 14 tooling controls,
14 existing Lean/cache tests, 11 experiment tests and five integration/admission
tests all report OK. Actionlint 1.7.7 reports zero errors across all six workflows;
shellcheck and pyflakes were explicitly disabled, so their checks are not claimed.
The isolated real warm installer log verifies the retained elan archive SHA and
reports elan4.2.4. The real warm toolchain log reports Lean4.35.0 at the full
eb6cafb7290e8bd5f2937522d8d804f58f02bafc commit and Lake5.0.0 from the same commit.
The coordinator reports curl was blocked in that isolated warm test. The reviewer
binds the exact logs without claiming to have independently executed that test.

SOURCE-CHECKS.json records a separate fresh read/hash check of the unchanged
1,386-module source manifest and the exact derived proof-cache base/snapshot.
No successful whole1386 hosted replay, successful pending analytic experiment,
or proof of the final arithmetic theorem is asserted by this acceptance.
