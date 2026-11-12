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

## Share every recorded failure without the artifact cache

Do not zip the entire audit run: it includes compiled libraries and caches. The
collector below reads every `.log` plus `summary.json`, `RESULT.json`,
`commands.json` and `plan.json` recursively. It does **not** invoke Lean, rerun
the audit, change its results, or copy build artifacts.

From the repository root in PowerShell, after obtaining this script:

```powershell
py -3 scripts\collect_windows_audit_failures.py --latest
```

For an explicitly selected run (recommended if several audits are running):

```powershell
py -3 scripts\collect_windows_audit_failures.py --run ".\audit-results\windows-YOUR-RUN"
```

Upload only the printed `audit-failures.zip`. It contains `failures.txt` and
`failures.json`, not raw logs or `.olean` files. Each recorded failure/candidate
has its original relative file path and, when available, line-numbered excerpts.
Nonzero stage/module exits are retained even without an `error:` line. Orphaned
logs, timeouts, Python/tool failures and runner exceptions are scanned too.
No failure-record count cap is applied. Markers in quoted text can be false
positives and are labelled as candidates.

By default, excerpts are limited to 8,192 characters per log, with initial
error context and the log tail. The report explicitly marks excerpts as partial
and reports the full diagnostic-fragment count; only the first 40 matching line
numbers are retained. For fuller context use `--excerpt-chars 32768` (maximum
65,536). Original logs are left untouched. Missing/unreadable logs, corrupt
metadata, skipped symlinks, changed-while-reading logs and decoding replacements
are reported rather than hidden. Exit code 2 means collection had problems;
its ZIP can still be shared, together with the listed missing originals.

The collector covers **recorded** failures, not hypothetical errors in modules
blocked by an earlier failure. A packet stops at its first failing module. A
`RUNNING` summary may represent an interrupted or still-running audit; stop/wait
for the audit and collect again for a stable snapshot. A toolchain failure before
the runner creates a results folder exists only in the terminal output, so share
that terminal error separately. Reports can contain local paths and source
excerpts; review before sharing outside this debugging conversation.

Collector tests (synthetic fixtures only, no Lean):

```powershell
py -3 scripts\test_collect_windows_audit_failures.py
```
