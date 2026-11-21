# Exact TZ mean replay r4: 5 directly diagnosed proof owners

Predecessor source intake 58e4a502b5aa979cf2c3427ce701fa8846e514d4120f7b34b9e6857c63096bd1.
Observed exact run 44854557710: 25/39 compile, 399 declarations
audited, five direct errors, nine blocked, 91 unselected. The inventory
and raw logs SHA are checked per owner by repair.py. Physical inventory
remains 130 Lean files; all 125 peers, all import lists, and exact
selected 39-name ready order are byte-/value-matched. Standalone
source patch only; no Lean run or GitHub operation by this author.

- ExactZeroIntegerGrid exposes the same Int cast cancellation already
  in the injective axis function, and simplifies the let-bound filter
  before Finset.sum_filter rather than rewriting by a term.
- MultiSieveCell directly elaborates the Bool=true branch as the
  actual Int divisibility, avoiding simp's stuck Decidable True
  under the Nat→Int cast; separates the | * parser token.
- OneAxisLocalDual uses the original ordered endpoints and both
  original Bool vertices. Names evaluation at the unique Fin 1 index
  and changes to the literal product rather than simplifying through
  dependent Equiv/Prod.map wrappers. A local named integrand is a
  let, not opaque have, so both original nested sums reduce.
- RetainedHorizon casts n≥1 with a typed Int inequality before
  applying positive multiplication.
- SignedGridPushforward changes the local root filter to its
  definitional body; both matching fibre mass sums simplify in the
  original product of reciprocals without rewriting competitors into
  the inverse of a whole product.

No API, public statement, analytic scope or cutoff changes. In
particular, this does not certify any formerly blocked module or
the full nonlinear/transference proof.
