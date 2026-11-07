# Checked proof-progress checkpoint

This directory is a dependency-closed source snapshot of the completed proof packets at the November 7 soundness-integration checkpoint. It is **not** a proof of the full integer-characterization theorem. The original polynomial and source-equivalence files elsewhere in the repository are unchanged.

## What is now proved

- **Literal 326:** the actual 296 quadratic rows, unique eight-coordinate lift, projection to 318, exact degree 4, and equality with the published 3157-term coefficient table. This goes beyond the earlier abstract constant-lift lemma.
- **Actual global elliptic arithmetic:** the displayed curve over Q(sqrt2), its first descent, dual square-abscissa theorem, finite generation, free rank 1, full 2-torsion and the odd saturation index. The finite generator search is kernel checked, not a rank oracle or native evaluation.
- **Actual heights:** normalization of Mathlib's absolute number-field height, exact polynomial/Mahler coefficient coverage, x-height of P = log 41, exact duplication constants 392/676, and the canonical-height limit with its integer quadraticity and comparison bounds.
- **Literal source labels:** `ActualGlobalGenerator318.source_global_labels` needs only the literal final318 source constraints. It gives four odd root labels, scalar orientation and huge anchor bound, and the common-torsion H/V labels.
- **Odd-index product height:** `ActualOddProductHeight318.odd_multiple_height_product` proves the actual absolute-height identity without a local-sign assumption. It includes a directly constructed formal subgroup at every integral finite place, including residue 2, and the exceptional D-small regular subgroup.
- **Detector height transfer:** the actual norm/shifted-trace three-scale bound transfers to the actual product height, including the final 49/(8k) exponent. The necessary nonzero base parameter remains explicit.
- **Complete local/source soundness joins:** one coherent source-label object fixes signs before primes are chosen. Actual split/inert logarithms, all three contact chains, and integer targets now give the high p^13, low p^4 and scalar p^8 divisibility statements. The rational-contact radical and actual three detector scales yield all required height comparisons from the named geometric input.
- **Lucas growth and witnesses:** integral Vieta descent and actual recurrence congruences prove the required logarithmic growth, including negative parameters. The exact completeness choice k=2(s−2) gives positive odd Lucas witnesses for odd s≥3 with s≡1 modulo three.
- **Published-polynomial soundness with one premise:** `LiteralSoundness318326.polynomial318_soundness` and `stored326_soundness` prove that zeros of the actual 318 polynomial or stored 3157-term 326 table have integer input, conditional only on `ContactHeight318.FiveContact49Height`. This geometric theorem is explicitly defined and is **not proved** by this checkpoint.
- **Completeness and49/8 components:** checked finite budgets, CRT/anchor/producer fragments, integral scaled-series machinery, exact contact determinants and metric/curvature/growth inequalities. Their global theorem dependencies remain explicit.

The manifest lists every included source, its hash, its producer and the topological build order. Producer receipts and independent bounded reviews are preserved under `receipts/` and `reviews/`. They are dated, scoped records: an earlier receipt's remaining-input list may have been closed by a later packet. The current status is described here, not inferred by adding declaration counts.

## What remains

1. Complete the global five-contact height producer with exponent 49/8. Exact metric cancellation, normalization corrections, isogeny-height transfer and finite constants are checked, and the source-level metric producer has been independently reviewed. These do not themselves construct the required models, covering fields, modular-support objects or global Arakelov/Yuan data.
2. Complete the formal integer-to-source witness existence direction. Prime-pattern/restricted-converse source audits and checked finite producer fragments are not yet a full Lean construction of every witness.
3. Compose these into an unconditional replacement for the existing `sourceArithmetic` assumption, then run the end-to-end clean rebuild and independent final review.

No overall completion percentage or time-to-proof follows from the number of checked modules. The remaining global geometric and existence inputs are substantial, not merely a few missing tactic lines.

## Reproduce

The snapshot pins Lean 4.35.0 and Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679. With Lean installed:

```sh
cd quartics/quartic-318-326/proof/progress
python3 verify_manifest.py
lake exe cache get
bash replay.sh
```

`replay.sh` kernel-checks every source in dependency order, then recursively audits all declarations, allowing only `propext`, `Classical.choice` and `Quot.sound`. It uses neither `sorry` nor native evaluation. The full finite enumeration is deliberately expensive. `bash replay.sh --audit-only` audits already built artifacts and does not claim a fresh source rebuild.

For this checkpoint, the 44 new or changed modules were freshly rebuilt inside this snapshot with kernel checking. Earlier producer packets were separately checked. The full333-module snapshot was hash/import-checked and recursively audited using those artifacts. The exact combined result and repository-check results are recorded in `checkpoint-verification.json`; it distinguishes that combined audit from a fresh rebuild of every snapshot module. Compiler binaries and the pinned Mathlib cache are trusted inputs.

## Exclusions

Exploratory/debug files, local `.olean`/`.ir` artifacts, dependency caches, browser/download scratch files, and still-live geometric/fiber-field/embedded-disc/Wronskian work are excluded. No PR is created by this checkpoint.
