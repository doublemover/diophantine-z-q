# Native Windows proof audit

This entrypoint uses the repository's existing source-admission, cohort, recursive-axiom and experiment checkers. It rebuilds the progress modules from source with kernel checking enabled and checks every packet listed as active at run time. It does **not** independently rebuild the Lean compiler or upstream Mathlib/package artifacts. They are trusted inputs. Passing is not a proof of the full arithmetic theorem.

## Prerequisites

Use native x86-64 Windows, 64-bit Python 3.10 or newer, Git, and the pinned Lean/Elan toolchain. In the progress project's directory, prepare the exact pinned package checkouts and official cached artifacts as described in its README (`lake exe cache get`). This preparation can require network access and disk space. The audit adapter does not fetch package artifacts: missing imports fail and are logged. Install the pinned toolchain in advance: the audit resolves the installed toolchain binary directly and fails if it is absent; it does not invoke an Elan shim. It honors an explicit `ELAN_HOME` first (and fails rather than silently ignoring an invalid setting), otherwise checks this checkout’s `audit-tools/elan`, then the default `$HOME/.elan`. It does not search a different checkout. For a custom location, set `$env:ELAN_HOME = "C:\path\to\elan"` before running. The selected absolute `lean.exe` is recorded in the run summary. Do not run another process that changes the checkout or its package/build trees during the audit. Keep enough free disk space for overlapping cohort artifacts, logs and packet outputs; no safe peak bound is provided here.

Clone with Git and leave the tracked checkout unmodified. Exact source bytes are checked against the project and packet manifests before compilation. Do not manually normalize line endings. From the repository root in PowerShell:

```powershell
py -3 scripts\windows_audit.py
```

Each run creates a new `audit-results/windows-...` folder without overwriting earlier results. Its `summary.json` has `PASS` only when every planned clean cohort, the combined recursive axiom audit, and every active packet check succeeds. Individual stage logs and the baseline and packet outputs are preserved there. The script rechecks HEAD, tracked-tree cleanliness and active packet intake hashes at the end; this does not make concurrent edits safe. A failure or interruption does not constitute a pass; an interrupted run may retain `RUNNING`. The process exits nonzero on recorded failure. Inspect the first failed stage log and any exception log.

The scheduler runs up to the number of logical processors in parallel, with one Lean thread per compilation, and specifies no process memory cap or wall-clock deadline. Dependency ordering means not every core is busy throughout. Lean's own source options and operating-system resource limits still apply. A full run may consume substantial memory and disk.

The adapter's focused Python tests can be run without Lean using `py -3 scripts\test_windows_audit.py`. These tests do not establish native Windows end-to-end compatibility or audit success.
