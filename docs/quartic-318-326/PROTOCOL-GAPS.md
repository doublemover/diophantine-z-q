# Contribution review against the new upstream protocol

Assessment target: contribution at `629861c8f61c870acad7480054928e3a7316e709`, after merging upstream `52bcd6475d61c25f0270d8abc1dcab9040bf0ba9`.

Status: **incomplete protocol assessment and incomplete mathematical work, not approval to submit or merge**. No pull request is being opened. This is an integrator's evidence/gap inventory, not an independent acceptance of the proof or of the integrator's own changes.

The active mathematical dependency target is **Version 13**. Its unchanged Kato construction/index/norm/class interface originates in Version 11. The [exact version comparison and separate reuse assessment](protocol-inventory/VERSION-CHANGES.md) distinguish inherited inputs from the new 498/514 and 394/411 reductions; those reductions are not automatically this contribution's 318/326 route. The [initial application and findings inventory](protocol-inventory/APPLICATIONS-AND-FINDINGS.md) records seven actual chains and six findings with [source bindings](protocol-inventory/evidence.json). It is explicitly nonexhaustive. Unrelated proof expansion is paused while these requirements and actual consumers are reconciled.

The [findings reconciliation ledger](protocol-inventory/FINDINGS-LEDGER.md) and [129-directory audit intake catalog](protocol-inventory/audit-intake.json) preserve concrete open concerns, earlier scope corrections and exact evidence hashes. This initial catalog does not establish exhaustive audit intake or resolve its open items.

## Requirements checked

The controlling documents are [the contributor guide](../../CONTRIBUTING.md), [research review guide](../research-review/README.md), [protocol version 1.1](../research-review/PROTOCOL.md), [application-binding protocol](../audit-history/PROTOCOL.md), and [PR template](../../.github/pull_request_template.md).

The public ruleset was read on 2026-11-08. Ruleset 26781429 was active for upstream main and required `Protocol / independent agent audit` from GitHub App 5663093, together with the named computational/build checks. Existing green CI cannot supply that decision. The ruleset must be checked again when a PR exists; no such PR or protocol-App acceptance is claimed here.

## Template evidence and remaining work

1. **Exact revision, scope and dependency impact: partly covered.** The contribution package has `INTEGRATION.json`, coefficient/input manifests, a dependency-closed `proof/progress/checkpoint-manifest.json`, and scoped checkpoint verification. Historical source identities are preserved. A final claim inventory still needs to connect each announced mathematical result to its exact statements, dependencies and consumers. The integration file describes the original import and must not be mistaken for a new final release manifest.

2. **Complete proof and source-application inventory: not established.** The source construction and conditional Lean endpoints are explicit, but actual global geometric realization and complete integer-to-source witnesses remain open. The existing arithmetic narrative, component-obligation document and bounded source reviews are evidence, not proof that every cited and uncited external application is inventoried. A complete nine-obligation application inventory and an independent omission review have not been located in this contribution. The upstream manuscript's accepted application contracts do not automatically cover our changed construction.

3. **Explicit computation and reproduction: substantial evidence, bounded scope.** The actual 318/326 tables, generators, input hashes, independent finite checks, exact degree/source-equivalence theorems, pinned Lean/Mathlib sources and recursive axiom audits are present. The 1,036-module checkpoint passed its full imported audit; recovery reused 882 exact-source CI artifacts and freshly rebuilt 154 modules. This is not a claim of a new clean 1,036-source build. Hosted clean mode and full coverage auditing exist. Computation does not discharge `sourceArithmetic` or the named geometric input.

4. **Non-author decisions and exact bindings: partly covered.** The frozen intake catalogs 129 published review directories. Bounded reviews frequently bind exact sources and disclose imported dependencies, but a sampled receipt does not establish complete coverage or independence. Some older records do not carry all model/task identity, tools, author, edit-fingerprint and downstream-binding fields now requested. Unknown metadata must remain unknown. Recovered semantic reconstructions require fresh replay and reviewer-authored new bindings; exact-byte recovery may preserve a source binding but does not reconstruct a missing log. Do not replace old approval hashes to imply a new acceptance.

5. **All audits, findings and resolutions: reconciliation required.** Dated reviews and corrections are preserved, and the new contribution findings ledger catalogs the published archive plus all three currently listed upstream issues and their six comments. This is not a claim of exhaustive private/conversation coverage or that every item is resolved. Continue reconciling received reports, unfavorable findings, later corrections and direct sanity-check questions against recorded dispositions. Distinguish prior justification from its actual incorporation and keep unresolved findings open.

6. **Final integration/closure: not complete.** No independent assembled-proof closure review of an unconditional 318/326 integer-characterization theorem exists here. Component approvals and a large number of checked declarations cannot replace that review. The stated remaining geometric/PEL, controlled integral and witness-construction inputs must be completed or kept explicitly conditional before the final claim can satisfy the completion standard.

## Concrete dependency adoption and source checks

The separately reviewed [Version 11 adoption](v11-consumer-binding/APPLICATION.json) compares the complete required index domain, both norm cases, fixed lattice multiplier and exact retained class consumed by Kato's bound. It also identifies the literal all-288-row completeness target and the already checked finite 326 lift. The [Version 13 amendment](v13-consumer-binding/APPLICATION.json) carries that narrow interface forward to the current manuscript with exact passage comparisons and distinct decisions. Historical Version 10/11 files and verdicts remain unchanged. This is not complete validation of the restricted converse or construction of all source witnesses.

The following public records distinguish author inventories, bounded source checks and actual non-author consumer decisions:

- [PP/analytic inventory](protocol-inventory/pp-analytic/REVIEW.md) and [independent conditional PP-to-318 consumer review](protocol-inventory/pp-consumer-review/REVIEW.md).
- [Hodge/Arakelov inventory](protocol-inventory/hodge-arakelov/APPLICATIONS-AND-FINDINGS.md), including a fresh published Javanpeykar comparison, and the separate [final published Gaudron–Rémond comparison](protocol-inventory/final-source-comparison/REVIEW.md).
- [Pan modularity interface](protocol-inventory/pan/REVIEW.md), [Brinon–Conrad application](protocol-inventory/brinon-conrad/REPORT.md) with a separate V13 carry-forward, and [Conrad character application on V13](protocol-inventory/conrad-characters/REPORT.md).

Final-version comparisons remain explicitly incomplete where only author text or published corroboration was accessible. Preliminary notes are not relabeled published articles. Source review of these implications does not construct the actual PEL surface, integral/metric comparison, or complete arithmetic witnesses. Further source and omission checks are in progress.

## Immediate sequence

- Preserve the 31 recovered modules and their completed fresh packet checks, then obtain missing exact consuming-join reviews without expanding their scope. Send combined verification to hosted CI first; do not duplicate the full replay on the cloud workstation.
- Complete the current Version 13 application/source inventory and classify every remaining publication or actual-construction gap into the next proof tasks. Preserve the narrow Version 11 repair as history.
- Reconcile the existing review archive into a findings ledger and identify missing reviewer/source metadata honestly.
- Resume prioritized proof work once the baseline, inherited-input comparison and objection triage identify the work actually needed. The remaining mathematical inputs are tasks to finish, not prerequisites that must already be proved before proof work can resume. After finishing, freeze the assembled revision for genuinely non-author closure review and relevant clean reproduction.
- Only if the user later requests a PR, fill the template with these exact evidence links and obtain the designated App's decision on that PR revision. No PR is authorized by this document.

## Checks already performed after the upstream merge

- Historical/application record check and its 7+19 rejection controls: PASS. These verify bindings and structure, not mathematical truth or complete source coverage.
- Original Version 13 inventory and all 10 original negative controls: PASS through the hash-bound minimal-fixture wrapper; all 85 files inspected by positive validation are retained.
- Version 13 portability tests: 12 PASS. Full 394/411 packaged source/table replay: PASS.
- Full 498/514 and 318/326 finite reproductions: PASS under official SHA-verified Node 26.13.0.
- Reviewed upstream Version 13 manuscript, application contracts and validator bytes: preserved unchanged.
- Hosted research checks at 09e35ad passed. The complete prior 1,036-module hosted progress run 42444536391 passed. The new 1,067-module hosted run 42447653546 remains in progress. Windows/paper/full proof results are not inferred from the local checks above.
