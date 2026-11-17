# Source-integration recovery checkpoint

This checkpoint records the source cut `1e0a8ffb3a3e2cd7d40fcaae2767e4e2d1ba1f77`, with arithmetic r144, geometry KS69, norm46, and the reviewed cleanup differential runner. It is recovery metadata, not a new mathematical checkpoint or proof result.

The JSON preserves the exact active-packet registry order, all 16 reachable packet subtree identities, and the raw independent integration/serial review and verified-publication receipt bytes for the four named cuts. Receipt hashes are checked before interpreting their content. Publication records are cross-bound to their archived serial gates. The earlier reviewed integration-helper receipt is retained as provenance, not as a grant of permission.

Run from a checkout with the recorded source history available:

```sh
python scripts/check_integration_recovery.py --repo . quartics/quartic-318-326/proof/recovery/integration-checkpoint-20261117-r144-ks69-norm46.json
python -m unittest discover -s scripts -p test_integration_recovery.py
```

The verifier makes no network calls and performs no fetch, checkout, index, branch, or remote mutation. It checks reachable serial commit parents/trees, packet identities and order, diagnostic file images/preimages, unchanged request markers, receipt byte hashes, and publication-to-review bindings. The regression tests use only disposable temporary repositories.

A successful result establishes these source-recovery identities only. It does not independently reproduce historical remote readbacks, authenticate compiler/audit outcomes, prove a theorem, discharge global rational-infinitude inputs, or approve a future push. Full strict target compilation and recursive allowed-axiom auditing remain separate obligations. The cleanup differential is not production proof acceptance.

Some local constituent commits are not ancestors of the published branch. Recovery must use the reachable gated packet subtrees and exact archived receipts rather than pretend that missing constituent history has been recovered. The script intentionally does not require or fabricate those unrelated local histories.

This checkpoint is anchored, not live: later branches and markers may advance normally. Do not interpret its older queue context as current run status, and do not overwrite it to conceal a later correction. Future checkpoints should have new identities.
