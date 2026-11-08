# Contribution review against the new upstream protocol

Assessment target: contribution at `629861c8f61c870acad7480054928e3a7316e709`, after merging upstream `52bcd6475d61c25f0270d8abc1dcab9040bf0ba9`.

Status: **incomplete protocol assessment and incomplete mathematical work, not approval to submit or merge**. No pull request is being opened. This is an integrator's evidence/gap inventory, not an independent acceptance of the proof or of the integrator's own changes.

The mathematical dependency target is **Version 11**, particularly its repaired Kato construction/index/norm/class interface. Version 13 is the latest merged repository state, not a substitute mathematical target. The [initial application and findings inventory](protocol-inventory/APPLICATIONS-AND-FINDINGS.md) records seven actual chains and six findings with [source bindings](protocol-inventory/evidence.json). It is explicitly nonexhaustive. Unrelated proof expansion is paused while these requirements and actual consumers are reconciled.

## Requirements checked

The controlling documents are [the contributor guide](../../CONTRIBUTING.md), [research review guide](../research-review/README.md), [protocol version 1.1](../research-review/PROTOCOL.md), [application-binding protocol](../audit-history/PROTOCOL.md), and [PR template](../../.github/pull_request_template.md).

The public ruleset was read on 2026-11-08. Ruleset 26781429 was active for upstream main and required `Protocol / independent agent audit` from GitHub App 5663093, together with the named computational/build checks. Existing green CI cannot supply that decision. The ruleset must be checked again when a PR exists; no such PR or protocol-App acceptance is claimed here.

## Template evidence and remaining work

1. **Exact revision, scope and dependency impact: partly covered.** The contribution package has `INTEGRATION.json`, coefficient/input manifests, a dependency-closed `proof/progress/checkpoint-manifest.json`, and scoped checkpoint verification. Historical source identities are preserved. A final claim inventory still needs to connect each announced mathematical result to its exact statements, dependencies and consumers. The integration file describes the original import and must not be mistaken for a new final release manifest.

2. **Complete proof and source-application inventory: not established.** The source construction and conditional Lean endpoints are explicit, but actual global geometric realization and complete integer-to-source witnesses remain open. The existing arithmetic narrative, component-obligation document and bounded source reviews are evidence, not proof that every cited and uncited external application is inventoried. A complete nine-obligation application inventory and an independent omission review have not been located in this contribution. The upstream manuscript's accepted application contracts do not automatically cover our changed construction.

3. **Explicit computation and reproduction: substantial evidence, bounded scope.** The actual 318/326 tables, generators, input hashes, independent finite checks, exact degree/source-equivalence theorems, pinned Lean/Mathlib sources and recursive axiom audits are present. The 1,036-module checkpoint passed its full imported audit; recovery reused 882 exact-source CI artifacts and freshly rebuilt 154 modules. This is not a claim of a new clean 1,036-source build. Hosted clean mode and full coverage auditing exist. Computation does not discharge `sourceArithmetic` or the named geometric input.

4. **Non-author decisions and exact bindings: partly covered.** There are 117 receipt files across 126 review directories. Bounded reviews frequently bind exact sources and disclose imported dependencies, but a sampled receipt does not establish complete coverage or independence. Some older records do not carry all model/task identity, tools, author, edit-fingerprint and downstream-binding fields now requested. Unknown metadata must remain unknown. Recovered semantic reconstructions require fresh replay and reviewer-authored new bindings; exact-byte recovery may preserve a source binding but does not reconstruct a missing log. Do not replace old approval hashes to imply a new acceptance.

5. **All audits, findings and resolutions: reconciliation required.** Dated reviews and corrections are preserved, but no contribution-wide findings ledger was located. This is a coverage gap, not a finding that any particular objection was deliberately omitted. Reconcile every received report, unfavorable finding, later correction and direct sanity-check question against a recorded disposition. Distinguish prior justification from its actual incorporation and keep unresolved findings open.

6. **Final integration/closure: not complete.** No independent assembled-proof closure review of an unconditional 318/326 integer-characterization theorem exists here. Component approvals and a large number of checked declarations cannot replace that review. The stated remaining geometric/PEL, controlled integral and witness-construction inputs must be completed or kept explicitly conditional before the final claim can satisfy the completion standard.

## Concrete dependency comparison now required

The contribution still cites pinned Version 10 restricted-converse/Kato material in `quartics/quartic-318-326/docs/arithmetic.md#kato-scope` and `proof/components/arithmetic-obligations.md`. Upstream Version 11 explicitly repairs the larger Kato index domain and the identity of the limiting class consumed downstream. Compare our actual consumers with that repair: quantify the complete required domain, identify the construction support, verify both norm/transition cases and any scalar factors, and identify the resulting class and coordinate ideal. Record an application contract and a non-author decision for the precise resulting route. Merely merging Version 11 files does not carry that acceptance into our pinned argument. This assessment has not determined that the conditional Lean statements are false.

Publication-version coverage also needs explicit reconciliation. For example, the retained Javanpeykar sign review identifies the exact source it inspected as arXiv:1403.6404v1. The completion standard requires comparison with the authoritative published theorem and corrections, or a linked project proof of needed unpublished content. Do not relabel an inspected author version as a checked final publication.

## Immediate sequence

- Preserve the 31 recovered modules and their completed fresh packet checks, then obtain missing exact consuming-join reviews without expanding their scope. Send combined verification to hosted CI first; do not duplicate the full replay on the cloud workstation.
- Build the application/claim inventory from the actual source and consumers, starting with the Version 10-to-Version 11 dependency comparison and the remaining geometric inputs.
- Reconcile the existing review archive into a findings ledger and identify missing reviewer/source metadata honestly.
- Finish the mathematical inputs, then freeze the assembled revision for genuinely non-author closure review and relevant clean reproduction.
- Only if the user later requests a PR, fill the template with these exact evidence links and obtain the designated App's decision on that PR revision. No PR is authorized by this document.

## Checks already performed after the upstream merge

- Historical/application record check and its 7+19 rejection controls: PASS. These verify bindings and structure, not mathematical truth or complete source coverage.
- Original Version 13 inventory and all 10 original negative controls: PASS through the hash-bound minimal-fixture wrapper; all 85 files inspected by positive validation are retained.
- Version 13 portability tests: 12 PASS. Full 394/411 packaged source/table replay: PASS.
- Full 498/514 and 318/326 finite reproductions: PASS under official SHA-verified Node 26.13.0.
- Reviewed upstream Version 13 manuscript, application contracts and validator bytes: preserved unchanged.
- Hosted checks on the latest merge are separate execution results and remain to be monitored. Windows/paper/full proof results are not inferred from the local checks above.
