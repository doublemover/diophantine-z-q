# Optional pre-commit lint for staged Lean packets

From the repository root, invoke the checker against **the Git index**. It does
not check unstaged edits, fetch dependencies, run a full proof audit, or install
anything.

PowerShell, using an already-installed official Lean 4.35.0 binary:

```powershell
$env:QUARTIC_LEAN = "$env:USERPROFILE\.elan\toolchains\leanprover--lean4---v4.35.0\bin\lean.exe"
$env:QUARTIC_LEAN_MODULE_CACHE = "$env:LOCALAPPDATA\quartic-lean\module-cache"
python -I -B scripts/check_staged_lean.py
```

On another OS, set the same environment variables to its real pinned compiler
and an optional local cache directory. Pass the installed `lean` executable
itself, not an elan shim. Python 3.10+ and Git are required. Without an explicit
module cache, all affected prerequisites are freshly elaborated.

## Exact v1 scope

This first release checks standalone files in
`quartics/quartic-318-326/proof/intake/<name>/` and their staged manifest.
Internal prerequisites, reverse consumers, and exact named donor mappings in
a staged `docs/ci-*/CONTRACT.json` file are supported. Use
`--contract docs/ci-<name>/CONTRACT.json` for an already committed donor map.
Any affected module matching the changed source is genuinely elaborated again,
with kernel checking and `linter.unusedSectionVars` enabled and warnings fatal.
Only unchanged prerequisites may be restored from the module cache. Non-
standalone Lean changes and staged compiler/Lake pin changes are outside this
version's scope and block rather than looking green.

The command reports a JSON receipt and native diagnostics with staged file
names. The exit codes are 0 for a real PASS or an explicit N/A (no relevant
changes), 1 for a Lean error/lint, 2 for NOT RUN / BLOCKED (missing or mismatched
compiler/cache, unsupported layout, or the elapsed budget). The default budget
is 20 seconds and may be changed with `--budget` for a manual check. Git
operations and Lean jobs are bounded; complete cache verification time is
reported separately. No result substitutes for the hosted clean build or
recursive axiom audit.

## Mathlib and the cache

Core-only packets require no upstream bundle. For Mathlib or other external
imports, use a prepared bundle from the exact official dependency acquisition,
not the working directory's unverified Lake artifacts. Set
`QUARTIC_LEAN_UPSTREAM` to its extracted root and
`QUARTIC_LEAN_UPSTREAM_SHA256` to the independently recorded SHA-256 of its
`upstream.json`. The manifest must contain:

- `version: 1` and the `environment` ID printed by this checker (set before the
  missing-upstream exit), binding the compiler revision, platform, current
  staged input pins, flags and checker version.
- `roots`, the imported modules covered by the bundle, and `libraries`, their
  relative Lean module roots in search order.
- `files`, the exact relative path to SHA-256 mapping of every artifact in
  those libraries. Include all recursive imported dependencies and Lean
  sidecars (including `.ir.sig`), not just each top-level `.olean`. Unexpected files, ambiguous
  direct imports, changed bytes and symlinks are rejected.

No published run currently delivers a sealed upstream/project artifact bundle
for this hook. Until one is prepared, a Mathlib packet may correctly report
NOT RUN. An immutable local module cache can be shared by trusted workers on
the same platform. Entries are scoped by compiler, lock, upstream manifest and
transitive staged source/import content, not by moving branch name. An unrelated
HEAD advance does not invalidate a truly unchanged dependency. Do not populate
this cache by copying arbitrary old `.olean` files into it.

## Opt in only after a manual check

If there is not already a local hooks directory in use, and you want all your
commits in this checkout to use the first-release scope above:

```powershell
git config --show-origin --get core.hooksPath
git config --local core.hooksPath .githooks
```

If you already have hooks, integrate the checker in your existing pre-commit
instead of replacing its setup. There is no auto-install. Review the configured
hook scope before opting in: unsupported Lean changes will be reported as
BLOCKED. The same command can be run manually without changing Git configuration.

Run the fixtures with `python -B scripts/test_staged_proof_hook.py -v`. Real Lean
fixtures exercise staged-vs-unstaged changes, the native unused-instance warning,
wrong/absent environments, foreign manifest and cache data, and content reuse
after HEAD changes. Real tests skip when the pinned compiler is not configured;
that is not a native verification.

## The Hodge Linux artifact pilot

The exact one-shot producer covers only the seven unchanged prerequisites of
`OriginalMarkedHodgeTensorHeight318`, the twelve official Mathlib roots needed by
that actual r7 leaf, and their compiled import closure. It starts with no
project module artifacts, strict-checks the real leaf, and seals dependency
artifacts only after success. The separate consumer verifies the original ZIP
against the producing run's authenticated artifact digest, validates the
archive members, and compares a cold dependency build with warm imported
dependencies. It always re-elaborates the changed r7 leaf; it also checks that
the exact earlier r6 bytes still fail on both native unused-instance lint
errors. This is a Linux x86-64 lint accelerator, not broader packet coverage,
or a formal proof acceptance.

A second worker should obtain the original, unextracted artifact ZIP using the
authenticated producing run, capture its authenticated digest, run ID, the
run's exact head commit and that commit's tree via the repository API, and run this in a clean Linux checkout containing the same reviewed source
pins:

```sh
python -I -B docs/ci-hodge-compiled-imports-once/run.py consume \
  --lean "$QUARTIC_LEAN" --artifact-dir "$ORIGINAL_ZIP_DIRECTORY" \
  --zip-sha "$AUTHENTICATED_ARTIFACT_DIGEST" --run "$PRODUCER_RUN_ID" \
  --producer-head "$AUTHENTICATED_HEAD" --producer-tree "$AUTHENTICATED_TREE" \
  --output "$ABSOLUTE_OUTPUT_DIRECTORY"
```

This validates each archive member on import and reuses the verified isolated
readonly snapshot for all three samples, with no repeated whole-library
hashing between samples. The manual standalone hook validates its input
bundle bytes per independent invocation, deliberately fail-closed. Do not
point it at a mutable or unauthenticated unpacked download.

For continued use after the canary, trigger rebuilds only for changes to the
covered *transitive* source paths, repository toolchain, package locks, exact
build/format flags or producer recipe. Changes to unrelated proof documents
need no build. A worker should select the latest compatible **successful**
producer with authentic run/job/attempt/workflow provenance and matching
compiler, architecture, lock, source-closure and artifact hashes, not blindly
select the latest run or branch head. Deduplicate by closure content identity,
so unchanged modules remain reusable after unrelated changes. Validate an
authenticated artifact once into a controlled read-only cache; repeated
imports may reuse that verified same snapshot, with validation redone on any
replacement or observed drift. Keep authoritative cold proof gates independent
and never accept a failed producer's partial artifact. No native shared
libraries are exported in this first pilot.

The artifact manifests record the Linux libc version for provenance. This
pure Lean format accepts a different libc only when exact system, architecture,
and pinned compiler identity match. It rejects native libraries outright.
