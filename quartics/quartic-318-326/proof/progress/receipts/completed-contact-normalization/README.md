# Actual quadratic contact normalization under DVR completion

Three modules, eleven public theorems and 45 exhaustively audited declarations, strictly rebuilt with `debug.skipKernelTC=false` and only standard recursive axioms.

## Actual base-change objects and maps

`ContactTensor318` constructs actual scalar-base-change algebra equivalences for the quadratic contact order and its unit-root normalization. It tracks both generators and proves equality of the entire contact-map square. This is not only a cardinality, rank, or chosen-root assertion.

`IntegralClosureTransport318` proves the general transport of both the order and candidate integral closure along compatible actual ring equivalences, while keeping the ambient algebra fixed.

`CompletedNormalization318` uses the actual maximal-ideal adic completion C of an actual DVR R. Its order is exactly C tensor R the original contact order. Its normalization is exactly C tensor R the original unit-root normalization. The actual whole-map square identifies their natural maps to the ambient generic fiber. The actual integral-closure property follows from the constructed completed DVR and explicit quadratic base-change equivalences. No general excellence or normalization-commutes-with-completion hypothesis is supplied.

The normalization is genuinely finite etale over C, and C is faithfully flat over R. For a nonzero contact parameter pi, an actual generic-fiber algebra equivalence and injectivity of the order map are proved. The equivalence agrees with the order map on every element. No claim that the possibly split quadratic algebra is a domain or field is made.

## Exact boundary

The abstract DVR and actual unit-times-even-power contact expression are inputs here. Previously checked source packets derive these from the normal model's actual height-one stalk and its finite even canonical valuation. The geometric identification of the actual source cover with this quadratic contact order remains explicit. This does not construct the global source cover, compactification, resolution, or final geometric realization.

The integral-closure statement itself does not require pi nonzero because it permits a noninjective order map. The stronger genuine generic-fiber identification and order injectivity explicitly require pi nonzero. In geometric use pi is an actual irreducible uniformizer, so that condition is available. Formal evaluation at positive contact order is handled separately by the completed-DVR evaluation packets.

## Replay

Run `bash run.sh`. It rebuilds all three files and audits every declaration of those modules, including constructed equivalences and generated helpers. The receipt binds sources, replay, log, and documentation. Generated Lean objects are not deliverables.
