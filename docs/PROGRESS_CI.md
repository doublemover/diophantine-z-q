# Progress-snapshot CI

`Progress Lean cohorts` checks the complete dependency-closed source snapshot in
`quartics/quartic-318-326/proof/progress`. It is separate from the older 48-helper
`Accepted Lean helpers and axiom audit` job. Ordinary 318/326 checks also validate
the progress source manifest, but that inexpensive validation is not a Lean replay.

## Parallel and incremental runs

The planner validates the source manifest and actual import DAG. The default is
up to 16 concurrent hosted cohorts in each of three dependency stages, separated
at import depths 7 and 16. Later stages verify and import earlier stages' exact
artifacts. Imported files are not recompiled or reuploaded. Within each stage,
the allocator balances source-bound measured compilation seconds while rewarding
shared dependencies. Changed or unmeasured sources use a four-second scheduling
estimate. Timing hints never authorize cache reuse or change source fingerprints.

The first full hosted cold run at `0547a75` passed: all 882 source modules were
freshly compiled and all 17,291 declarations recursively audited. Its slowest
four-way cohort spent 39.7 minutes compiling. Nine independent finite-generator
chunks alone took 25.1 minutes in that one job. A count-based 16-way plan also
placed all nine together, so more runners alone did not remove that bottleneck.
The new early boundary distributes those nine chunks across nine foundation jobs.

For the 1,036-module snapshot, the timing-aware plan has 16 jobs per stage, with
maximum source counts 76, 37 and 144. Applying the measured 882-module timings
plus the fallback estimate gives stage critical-path compile estimates of 223,
334 and 304 seconds, about 14.4 minutes combined. This excludes setup, transfer,
queueing and the final audit, and is not a measured speedup. The extra stage adds
a setup/transfer barrier. Hosted runs must measure the complete tradeoff.

Manual runs can change `cohorts`, `max_parallel`, `early_depth` and `split_depth`
independently. Setting `early_depth` to zero selects two stages.
Four was a configured budget, not a desktop or GitHub limit. GitHub documents a
256-job matrix limit and standard hosted concurrency of 20 for Free, 40 for Pro,
60 for Team and 500 for Enterprise. The owner's actual account limit is not
assumed; other workflows share it and excess jobs queue. See
[GitHub Actions limits](https://docs.github.com/en/actions/reference/limits).
Only standard hosted Ubuntu runners are requested, not paid larger runners.
Each job uses one Lean compiler at a time, one compiler thread, a 6 GiB Lean
memory limit, and kernel checking enabled.

A module's cache fingerprint includes its source bytes, the recursive fingerprints
of its local imports, the exact Lean/toolchain and Lake dependency manifests,
compiler flags, checker version and platform. A cache hit additionally requires
the expected artifact hashes and the exact artifact hashes of its imported project
modules. Changes invalidate the affected module and its downstream dependents.
After the complete audit, a whole-snapshot cache is saved. Each cohort restores it
first, plus an independently completed cohort cache as fallback. Repartitioning
therefore does not discard valid modules merely because they moved between jobs.
For example, moving from 951 to 971 modules would otherwise miss 207 unchanged
modules under per-cohort-only caching. Only matching source/dependency/artifact
entries are admitted from either cache.
Whole-snapshot saves and restores use the same `.cache/progress-ci` path;
cohort saves and restores use `.cache/progress-cohort`. GitHub cache versions
include the path, so differing save/restore directories would cause misses even
with matching key strings. A workflow regression test checks this contract.
The checker never copies an unlisted cache artifact into the fresh build directory
and never uses an inherited project `LEAN_PATH`.

Cache reuse is not a new source compilation. Cohort receipts list separately every
compiled and reused module. These are trusted artifacts from repository CI, not
independent proof certificates. Upstream Mathlib artifacts remain trusted inputs,
with the original pinned source revisions checked. Missing listed upstream files
are built from those pinned sources with kernel checking enabled.

The final job verifies all cohort receipts, exact source coverage, artifact hashes
and shared-module byte agreement. It then imports the entire snapshot and runs the
exhaustive recursive axiom audit, including private/generated declarations. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. The uploaded result says
whether the run was incremental or clean. Neither status proves the outstanding
geometric realization or the full arithmetic theorem.

## Clean mode and resource behavior

Use the workflow's manual `clean` input to bypass all project-artifact reuse. Every
project module is then freshly kernel-checked within at least one cohort before
the combined audit. Upstream pinned caches are still used. Logs, timings and the
exact result are uploaded; no local desktop is required.

At most 16 cohort runners execute simultaneously by default. A running cold build is not
cancelled by the next push, so it can finish and populate caches; the latest pending
commit follows it. A failed cohort does not cancel the others. Runtime for the
whole snapshot must be measured from these runs, not inferred from the small
48-helper job or from module counts.

An actual three-module Lean smoke test checked cold compilation (three modules),
warm reuse (zero compilations), a source change (only that module and its dependent
rebuilt), and clean mode (all three rebuilt). Artifacts were byte-identical between
equivalent clean and incremental builds, and the complete final axiom audit passed.
A second real Lean test used two foundation cohorts and one dependent cohort.
Cold, warm, source-changed and clean staged builds all passed the complete audit;
the changed foundation source rebuilt its downstream module but not the independent
module, and imported prerequisites were not reuploaded. A further real Lean test
changed the cohort partition while restoring the complete audited cache: it
compiled zero unchanged modules. All five cold/warm/repartitioned/changed/clean
combined audits passed. Regression tests also reject disagreement between the replay module list and the
authoritative manifest. These small tests validate cache behavior, not full-run performance. A three-stage
real Lean test additionally changes A in A→B→D while leaving independent C
unchanged. Cold, warm, repartitioned, changed and clean runs compiled 4, 0, 0,
3 and 4 modules respectively, and all five complete recursive audits passed.
This checks actual three-stage cache invalidation, not just a mocked planner.

## Small-helper dependency setup

The older helper job now derives its upstream roots from the exact source manifest
instead of fetching all Mathlib artifacts. A fresh isolated download verified
3,131 upstream cache files (about 202 MiB), versus 9,031 in earlier full-cache CI
runs. That local download took 13.85 seconds; it is not a cross-runner wall-time
speedup measurement. Fresh CI must measure total setup, decompression and build
time. Project helpers still rebuild from scratch and undergo their full axiom
audit on every run.

## JavaScript runtimes

The repository's Node scripts are pinned to Node 26.13.0, whose official Linux
archive was SHA-256 checked and used for the construction and 318/326 finite
reproduction tests. Their results passed without changing the polynomial bytes.
The GitHub-maintained actions are independently pinned to current releases whose
`action.yml` explicitly declares Node 24: checkout 7.0.1, setup-python 7.1.0,
setup-node 7.1.0, cache 6.1.0, upload-artifact 7.0.2 and download-artifact 8.0.2.
Installing Node 26 for project commands does not change an action's embedded
runtime; these actions support Node 24 rather than Node 26. No forced Node-20
compatibility override is used.
