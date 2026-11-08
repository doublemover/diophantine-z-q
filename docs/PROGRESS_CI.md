# Progress-snapshot CI

`Progress Lean cohorts` checks the complete dependency-closed source snapshot in
`quartics/quartic-318-326/proof/progress`. It is separate from the older 48-helper
`Accepted Lean helpers and axiom audit` job. Ordinary 318/326 checks also validate
the progress source manifest, but that inexpensive validation is not a Lean replay.

## Parallel and incremental runs

The planner validates the source manifest and builds the actual import DAG. It
groups terminal modules into four dependency-closed cohorts, favoring shared
dependencies over naive equal-sized chunks. For the initial 882-module snapshot,
the cohorts contain 347, 220, 219 and 219 modules: 123 dependency compilations are
duplicated during a fully cold run, instead of 663 under a naive balanced split.
Each cohort runs on a separate GitHub-hosted runner, with one Lean compiler at a
time, one compiler thread, a 6 GiB Lean memory limit, and kernel checking enabled.

A module's cache fingerprint includes its source bytes, the recursive fingerprints
of its local imports, the exact Lean/toolchain and Lake dependency manifests,
compiler flags, checker version and platform. A cache hit additionally requires
the expected artifact hashes and the exact artifact hashes of its imported project
modules. Changes invalidate the affected module and its downstream dependents.
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

At most four cohort runners execute simultaneously. A running cold build is not
cancelled by the next push, so it can finish and populate caches; the latest pending
commit follows it. A failed cohort does not cancel the others. Runtime for the
whole snapshot must be measured from these runs, not inferred from the small
48-helper job or from module counts.

An actual three-module Lean smoke test checked cold compilation (three modules),
warm reuse (zero compilations), a source change (only that module and its dependent
rebuilt), and clean mode (all three rebuilt). Artifacts were byte-identical between
equivalent clean and incremental builds, and the complete final axiom audit passed.
Regression tests also reject disagreement between the replay module list and the
authoritative manifest. These small tests validate cache behavior, not the runtime
or success of the initial full hosted run.

## Small-helper dependency setup

The older helper job now derives its upstream roots from the exact source manifest
instead of fetching all Mathlib artifacts. A fresh isolated download verified
3,131 upstream cache files (about 202 MiB), versus 9,031 in earlier full-cache CI
runs. That local download took 13.85 seconds; it is not a cross-runner wall-time
speedup measurement. Fresh CI must measure total setup, decompression and build
time. Project helpers still rebuild from scratch and undergo their full axiom
audit on every run.
