# Independent review of the research-protocol setup documents

Decision: accepted within the documentation scope below.

Reviewer: `/root/astra_quartic_opt02_squares`, a model reviewer distinct from documentation author `/root/astra_quartic_opt10_combination`. Review date: November 7, 2026. The exact serving-model identifier is not independently attested here. The reviewer used read-only source inspection, Git comparisons, SHA-256 checks and the existing focused audit-history checker. The reviewer did not author or substantively repair these documents, edit either candidate repository, or publish a review through GitHub.

## Exact files reviewed

The acceptance covers these four file contents, identified by SHA-256 of the Git file bytes to be incorporated. The public and private copies were independently compared and match. The explicit line-ending correction below distinguishes the Windows working copy from its Git representation.

| Repository-relative path | SHA-256 |
|---|---|
| `.github/pull_request_template.md` | `c36bd6b0dbb13639f6028ff421a9c6e65b68badab1b3b758fd883397b81c338d` |
| `CONTRIBUTING.md` | `4606405b80cf1dc4eaebf078424e820865fbf68d87c0843ee0a0c5f79a7227b7` |
| `docs/research-review/PROTOCOL.md` | `f2111f716457de7f45183fdeeb0a801d9c53e8378e20d7ae94bcb3f479e0b003` |
| `docs/research-review/README.md` | `51cd25985139762b18a2bb442f926f163d4b8d678f883587d4546bc5b7decd2e` |

The starting public setup commit was `c8963c1c8c3e5485b4b40a1dfb838ff293125546`, based on `5bbd74f6a479776a332cbe036809d5dddae63720`. The private setup commit was `4ed4b7b78fafd6743a6ed516785af93483cfec18`, based on `4ac084cf820213b51ff57814fd348fe86e428890`. The final absolute-link template above was still an uncommitted change during this semantic review. These starting commit IDs do not pretend to bind that later template or the incorporation of this report; the four content hashes do.

Binding correction, November 7, 2026: the first version of this report listed `CONTRIBUTING.md` by its Windows working-copy SHA-256, `cd9b912f36b621b5fe3f7097837e89e527706382c9663907a26ac3869b518c76`. The integrator identified that Git stores the LF representation instead. I independently read both Git blobs and both working copies and verified that replacing exactly 32 CRLF line endings with LF reproduces the Git bytes exactly, with no other change. I explicitly accept the Git SHA-256 `4606405b80cf1dc4eaebf078424e820865fbf68d87c0843ee0a0c5f79a7227b7` in the table above. The first report is preserved separately as historical evidence. This is a reviewer-authored binding correction, not a semantic repair or an integrator refresh of an old verdict. The other three table hashes identify LF bytes directly.

The supplied source was the owner's “Mathematical research review protocol,” version 1.1, November 7, 2026. Its SHA-256 is `f2111f716457de7f45183fdeeb0a801d9c53e8378e20d7ae94bcb3f479e0b003`. The repository's `docs/research-review/PROTOCOL.md` is byte-identical to that source. This is a review of faithful adoption and contributor guidance, not a new claim that software can decide arbitrary mathematical truth.

I also read the existing `AGENTS.md`, `docs/audit-history/PROTOCOL.md`, and the current review record's scope limitation. Their hashes are respectively `8962f442f897f69d6f001a589eeae22881bda75b77f1b77e7f30f3b7d50e0bfb`, `c0b9834a75e64bfd66183b06d1e26019f957a38468ce41b10ce290f8c5c44816`, and `b5ea322583af1100d2d73f25a7185e42e747e76c5609f227331ecd03ab869eb9`. They are unchanged from both setup bases.

## Source-to-guidance review

All five requested completion requirements are present as requirements, not optional aspirations:

1. The full protocol requires complete proof modulo identified published theorems with checked applications. The contributor guide requires publication venue and authoritative version and project proofs for needed unpublished inputs. It requires unresolved assumptions to be stated instead of claiming complete verification.
2. The guide requires every cited application and substantive uncited external input, review of the inventory for omissions, and all nine application obligations. Those obligations include connecting maps, domain coverage, conventions, exceptional cases and the exact downstream object.
3. The guide requires explicit domains, simultaneous choices, algorithms, constants, inputs, certificates, commands and reproducible outputs. It distinguishes compressed or generated representations from full expansions and finite identities from their arithmetic applications.
4. The guide requires every received human or model audit and substantive objection, including unfavorable reports and follow-ups on closed issues. It requires reviewed repairs or independently checked rebuttals and preserves unresolved findings and prior verdicts. The unchanged full protocol supplies the detailed duplicate, vague-concern and scope rules. Neither votes nor silence resolve a finding.
5. The guide requires repeated independent audit, repair and integration through final frozen closure. It requires rechecking affected premises, consumers and computations, plus independent review of the assembled proof. A collection of component acceptances is not treated as final closure.

The PR template asks for the exact revision, hashes, changes, dependency effects, source/application inventory, explicit computation evidence, non-author decisions, complete audit findings and final integration review. It directs users to explain inapplicable items and identify incomplete work. The contributor entry point links both the practical guide and full protocol. Local document links and the two named protocol heading targets were checked against the reviewed files.

The independence requirements agree with the existing guidance. An application author cannot independently accept that application; another run by the same agent is only a repeat check. A reviewer who supplies a substantive repair needs a different non-author reviewer. Human and model review are explicitly distinguished, unknown model metadata stays unknown, and new file/dependency bindings require reviewer-authored acknowledgment. These documents impose no mandatory second human or GitHub-user approval. They support independent agent review while retaining the owner's separate publication authority.

## Findings and dispositions

Finding DOCS-1: the initial PR template used `../docs/research-review/README.md` and `../docs/research-review/PROTOCOL.md`. A template's text is inserted into a PR body; it is not rendered there as a file located in `.github`. Those relative targets therefore did not reliably identify the intended guide and protocol. This issue was reported during integration before this final semantic freeze.

Disposition: resolved by the documentation author. I inspected both initial targets and the final template. The final version uses the absolute public GitHub `blob/main/docs/research-review/README.md` and `blob/main/docs/research-review/PROTOCOL.md` URLs. Both repositories carry identical guide/protocol contents. The fix changes exactly those two targets on one line and is included in the template hash above. The URLs are navigation to the adopted main-branch documents after integration; they are not immutable review evidence. Exact review evidence remains the hashes in this report. I did not claim those new main-branch URLs were already live before the setup merge.

No other unsupported instruction, omitted completion requirement or unresolved substantive documentation finding was found in this review. That statement concerns this review's findings; it does not assert that no other audit or subsequent PR comment exists. Complete current/historical intake must still be reconciled by the final setup process.

## Mathematical scope, rollout and verification

Git comparison with each setup base shows exactly the four documentation paths above changed. The existing mathematical manuscripts, polynomial artifacts, formalization, review contracts and their scopes are not changed by this four-file patch. The existing guidance and both focused checker source files also remain byte-identical to their bases.

The guide explicitly preserves the current manuscript record's inherited qualifications and says installing the protocol neither expands its scope nor retroactively certifies the complete proof. It distinguishes structural checks, mathematical status and review coverage. The full App check is described as not yet active, while existing PR/CI requirements are described separately. Its planned result is bound to actual evidence and a recorded cutoff; the guide promises neither instantaneous later-comment detection nor an atomic comment-and-merge transaction. Those are honest statements of this rollout stage, not assertions that the new enforcement has already passed deployment tests.

I ran `python -B scripts/check_audit_history.py --self-test` from each repository root using the unchanged existing checker. Both returned exit code 0 and reported:

```text
PASS: 9 historical dispositions, evidence pins and manuscript passages. Not a mathematical proof check.
PASS: 7 negative controls rejected.
PASS: 19 application-review negative controls rejected.
PASS: 3 current application contracts, revision and follow-up records. Not a proof check.
```

I did not rerun heavy mathematical builds or claim a fresh whole-proof audit. The relevant conclusion is faithful documentation adoption, correct links after the identified fix, unchanged mathematical scope, and successful existing structural checks.

## Later final binding

This report accepts the four semantic file contents above. It is not its own receipt, does not contain a self-referential final-head hash, and does not accept an unseen final application or assembly packet. After the report and template are committed, the final complete manifests, changed-path coverage, application/dependency targets and exact report bytes must be inspected and explicitly adopted by an eligible non-author reviewer. Any semantic change reopens the affected review. No successful App check, merge authorization or mathematical whole-proof acceptance follows from this report alone.
