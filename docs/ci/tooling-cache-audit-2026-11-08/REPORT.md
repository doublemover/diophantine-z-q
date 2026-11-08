# CI workflow and tooling-cache audit, 2026-11-08

## Findings and fixes

The repeated setup downloads were not evidence that project proof caching was broken. In run 42463941507, attempt 2, job 128681736907 restored the complete audited 1,338-module cache and its cohort fallback successfully, then unconditionally fetched elan and received HTTP 504. Python 3.12.14 was absent from the fresh runner's local tool cache, so setup-python downloaded it before any existing project cache restore. Other failed jobs never reached Lean.

The audited workflows previously persisted project artifacts and the TeX bundle, but not Python, Node, elan, the Lean distribution, or the Tectonic executable archive. New GitHub-hosted jobs do not inherit a previous job's filesystem. setup-python's package-manager cache is not an interpreter cache.

Implemented:

1. Four shared composite actions restore exact-version tooling independently of project proofs. Python and Node restore the version directory, including the architecture completion marker, before the unchanged SHA-pinned setup action. Both versions are verified before an immediate cache save. No pip/npm project dependency cache is introduced.
2. The elan 4.2.4 release archive is SHA-256 checked on every use, then saved separately before Lean installation. The exact Lean 4.35.0 distribution is restored under its own key and its expected commit is checked. Only that compiler directory is cached, not all of `~/.elan`, credentials, settings, or Mathlib. The compiler cache is saved before fetching Mathlib to avoid archiving a combined large dependency tree.
3. Progress and experiment planning warm the compiler cache before matrix fan-out. The empty experiment matrix still skips compiler setup and all packet checks. A cache-save warning can still leave a downstream job cold; warm-up is an optimization, not evidence of guaranteed publication.
4. Tectonic's already checksum-verified release archive is cached separately from its TeX bundle. Paper rendering installs Poppler only if the required commands are absent. Existing engine, bundle, Node, Python, Lean, Mathlib and third-party action pins remain unchanged.
5. Optional tooling and TeX cache transport failures may fall back to the original setup/download path. SHA/version checks, source checks, compilers and proof audits remain fatal. No corrupt archive is silently executed or replaced with an unpinned version.
6. The exact pinned artifact downloader flattens pattern downloads when only one artifact matches. A tested layout normalizer now restores the folder expected by the existing cohort verifier. This fixes the manual one-cohort path without changing any bundle bytes or admission logic.
7. Failed cohort logs are uploaded with attempt-qualified names outside the verified-bundle download pattern. Successful bundles retain their existing names. Both are retained seven days instead of two. There is no destructive overwrite. The pinned SDK supports same-name artifacts across reruns and selects the latest ID per name; this change is provenance hygiene, not a claim that every rerun previously caused a name collision.
8. Accepted-progress source admission now uses the existing nested-comment/string parser, rejects source-level kernel-check overrides and unproved/unsafe escape declarations, and rejects Python `-O`. The same guard covers the combined audit source. Declaration-aware handling allows genuine definitions and expressions named `constant`. All current 1,386 source bodies pass. The private-inclusive audit remains required; this supplementary lint is not a replacement for Lean or code review.

## Complete workflow coverage

- `progress-lean.yml`: planning; three dependency stages; whole-snapshot and per-slot fallback cache restoration; verified cross-stage artifacts; final private-inclusive recursive axiom audit; complete-cache save. Runtime setup is now shared and warm before fan-out. Main concurrency intentionally lets the running run finish. GitHub retains at most one pending run for the group, so it does not promise to execute every superseded commit.
- `progress-experiments.yml`: explicit packet admission and exact baseline closure; isolated draft output; bounded per-source compilation and recursive packet audit. It may save tooling only through the shared actions. It never saves experiment proof artifacts to the accepted cache. Latest-commit cancellation is retained. Empty matrices remain skipped.
- `research-checks.yml`: Linux and Windows source replays, inventory checks, fixed 48-helper clean Lean build, and paper build. All exact Python/Node versions are retained. Lean tooling and Tectonic reuse the shared setup. Existing repeated finite checks are retained rather than silently pruning coverage.
- `check-quartic-318-326.yml`: finite construction/integration replay with exact Python and Node runtimes; no proof artifact promotion.
- `manuscript-integration.yml`: manually selected reproduction/paper/metadata modes, exact manuscript and source bindings, isolated historical checks, and PDF review. Mode selection, checks and pins are unchanged; runtime caches and conditional Poppler setup are added.
- `handoff-release.yml`: manual, original-repository-gated draft-release packaging with checksum-pinned historical baseline and archive replay. Its existing write permission is confined to that workflow; no new publication privilege is added. Runtime caching changes only setup. This fork does not satisfy the pre-existing original-repository guard.

No `pull_request_target`, privileged automatic release, new secret, or persistent credential is introduced. External actions remain full-commit pinned. GitHub cache access follows branch/default-branch/PR-ref scope; runtime caches have exact OS, architecture, image-family and version keys and no broad fallback. They contain public tools, not secrets. Like the existing project caches, hosted runtime caches are trusted repository-CI outputs, not independent cryptographic certificates for every extracted executable.

## Proof cache correctness and invalidation

The accepted checker still binds module keys to the exact compiler/dependency/checker/flags base, source bytes and transitive dependency keys. Reuse also verifies the actual dependency artifact hashes and cached output bytes. Cross-stage receipt compatibility, exact source coverage and the disjoint compiled/reused partition are rechecked. The final audit imports every module, including private/generated declarations, and checks recursive axioms. Experimental baseline reuse requires a complete previously audited cache and verifies only the exact needed closure; it does not claim the current whole snapshot passed.

No changes were made to `scripts/check_progress_lean.py`, `scripts/check_lean.py`, the 1,386 Lean sources, the compiler or dependency pins, or experimental source packets. The source snapshot and existing proof-cache keys remain:

`6c2e696a14020c40b912e3e572ce1d0cb056695a7e2928bc6029f1906c10f96b`.

The source-policy guard is run before planning/build/audit; adding that stricter guard does not require discarding valid artifacts for source bytes that already satisfy it. The standalone manifest command now explicitly requires the complete repository's `scripts/check_lean.py`, resolved independently of cwd.

## Validation

- 14 tooling/layout tests pass: cold-toolchain command selection, warm no-install path, wrong-version and changed-pin rejection, corrupt-archive rejection, optional-cache boundaries, exact runtime scopes, singleton/multiple/conflicting layouts, and workflow wiring.
- 14 existing Lean/cache tests pass, including transitive invalidation, warm reuse, clean rebuild, mixed-stage verification and cohort reassignment.
- 11 experiment admission/audit tests pass.
- 5 integration/source-policy tests pass, including the documented manifest cwd, optimized-Python rejection, negative kernel/axiom controls, and valid `constant` identifiers.
- The real cached elan archive and existing exact Lean/Lake distribution were exercised in an isolated HOME with curl blocked. SHA verification, installer execution, compiler commit and Lake version all passed without a download. The compiler directory was linked to the already installed release for this local test; this is not a hosted cache-transport test.
- actionlint 1.7.7, downloaded from its official release and checked against its release checksum file, reports zero errors across all six workflows. Shellcheck/pyflakes were unavailable and disabled; this is not a claim they ran. Shell syntax and YAML parsing were checked separately.
- Fixed 48-helper source checks and historical audit-history/negative controls pass. No broad local Lean-chain replay was used for this infrastructure change.
- Hosted cold/warm runtime restore and complete proof results for this patch remain pending at publication. A successful local mock or workflow lint is not a hosted PASS.

The independent bounded source review is preserved under `independent-review/`; it also leaves actual hosted validation pending.

## Retained limitations and costs

A first cold installation still needs the official download service. A warm cache still needs GitHub's cache service, and caches can be evicted or unavailable across scopes. Saving is best-effort and simultaneous first-time workflows can race to seed the same immutable key. No pin is relaxed to hide those failures.

Before this patch, the repository cache API reported 251 entries totaling 2,683,515,509 bytes. The exact Lean distribution is about 3 GB unpacked; its separate compressed cache adds storage and restore bandwidth. Saving it before Mathlib limits temporary disk pressure, but hosted timing/disk measurements must confirm the tradeoff. The TeX bundle and pinned Mathlib artifact service remain independent network dependencies. Caching the entire Mathlib tree was deliberately not added, because the previous workflow identified combined-archive disk pressure and the upstream cache already supplies content-addressed artifacts. Every cohort still obtains its required official environment; a future optimization of those upstream roots must preserve source and artifact identity rather than skip checks.

Seven-day cohort retention improves delayed retry support but is not indefinite. Once successful-stage artifacts expire, a failed-jobs-only rerun may require a new full run using the verified project caches. Project cache restoration itself remains fail-closed when an experimental required baseline cannot be obtained. Cache transport is not mistaken for proof acceptance.

The 1,386-module combined checkpoint is still pending, not retroactively passed. The prior attempt-1 evidence remains unchanged in `docs/quartic-318-326/hosted-1386-infrastructure-failure`. Attempt-2, separate research, and setup-only experimental failures are preserved unchanged under this report’s `evidence/` directory. The prepared next proof cutoff remains held until the baseline is actually sound.

## Source evidence

- [Main run 42463941507](https://github.com/doublemover/diophantine-z-q/actions/runs/42463941507), including attempt 2.
- [Research run 42464991462](https://github.com/doublemover/diophantine-z-q/actions/runs/42464991462).
- [Setup-only experiment run 42464991532](https://github.com/doublemover/diophantine-z-q/actions/runs/42464991532).
- [Pinned setup-python local-cache-first implementation](https://github.com/actions/setup-python/blob/6d4fd22b20465ccc0f7354476588e8df7c9ca0e0/src/find-python.ts).
- [Pinned setup-node distribution/cache implementation](https://github.com/actions/setup-node/blob/949feb2413d6458794dcd2491c4babbbce0c15c1/src/distributions/base-distribution.ts).
- [Pinned download-artifact singleton handling](https://github.com/actions/download-artifact/blob/9000827ccba6bdab643e8b6fd33ac0654aef8333/src/download-artifact.ts).
- [Pinned cache restore error handling](https://github.com/actions/cache/blob/55cc8345863c7cc4c66a329aec7e433d2d1c52a9/src/restoreImpl.ts).
