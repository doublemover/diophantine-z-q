# Supplemental Hodge project-only lint cache

This feature-branch workflow is an additional native lint, never an input to or
replacement for the fresh proof kernel and recursive axiom gates. It checks the
exact Hodge r7 staged leaf and seven pinned project prerequisites in
`contract.json`. It runs on trusted repository pushes to `add-quartic-318-326`
and exact covered source and recipe paths; ordinary docs and unrelated proofs
don't trigger it. It never runs on a pull request, and the checkout token is not
persisted. It does not configure anyone's Git hooks.

## What is cached

Only seven content-keyed project objects and their compiled Lean sidecars,
including `.ir.sig`, under the exact dedicated Actions cache path. No upstream
Mathlib package data, binary toolchain, source tree, Git configuration, or
credentials enter this cache. Official Mathlib inputs still use the pinned
upstream distribution. Each job hashes the fresh locked upstream files once
when creating an isolated snapshot; a subsequent lint validates that snapshot's
inventory and file identities without rehashing the whole library. The project
objects themselves are always content-validated.

The key includes the exact compiler/platform, lock and flags, checker and
producer recipes, official upstream content identity and all selected transitive
project source hashes and import edges. It does not key off Git HEAD, a mutable
branch label alone, or the last successful run. Only an **exact** reported hit
may be used, and every restored object and sidecar must validate. Partial hits
are discarded locally before regenerating. The warm changed file is always
elaborated, not served from cache.

A new key runs a second isolated validation job. It restores the same exact key,
checks the bytes against the first job's project catalog digest, demonstrates
zero prerequisite rebuilds, and lookup-tests a changed dependency key with no
write. The native test in a temporary copy also edits a covered dependency's
content and verifies that it and every affected consumer rebuild, while an
unaffected prerequisite remains reusable. It does not save the test key. A
later trusted push with an existing compatible key skips the extra validation
job, not the actual staged lint.

The first version intentionally supports this Hodge closure only. To accept
a new proof revision, review and advance the explicit coverage contract,
including approved path/SHA/import metadata and exact upstream roots; update
the workflow path fence when paths change. A lock/toolchain or unsupported
closure change blocks rather than silently selecting stale data.

The successful primary job also publishes these small project objects and
their receipt as a separate authenticated ZIP, so other compatible Linux
workers need not download the combined public upstream bundle. Verify its
artifact digest, producing run and contained project hashes. The small ZIP
does not supply the pinned official upstream library; check that exact
world independently before importing these project outputs.
