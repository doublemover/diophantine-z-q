# Exact original weighted period product, r4

Only the exact terminal changes from official run 44941513448 (13/14,
108 audited declarations and 33 verified baseline owners). Its sole
diagnostic was the rewrite of an explicit pullback function
`fun τ => w (q τ)` by a consecutive density theorem presented as
`w ∘ q`. Introduce the measurable explicit lambda, type the reverse
density identity separately using `withDensity_mul`, and rewrite with
that exact head. No density, weight, model, or hypothesis is changed.
All 13 accepted source files and the exact baseline order are retained.
No local Lean.
