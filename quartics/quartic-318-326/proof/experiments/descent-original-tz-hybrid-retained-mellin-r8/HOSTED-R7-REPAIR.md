# Exact TZ mean replay r8: sole directly diagnosed proof owner

Source predecessor intake dbb175df3ccc4b1684d40a00ef2b42926168be6e36c9538ee15aff17dbce4589.
Observed 35/39 compiled, 526 strictly audited declarations; both
r6 owners pass; GridMarginalJoin alone diagnosed and 3 modules blocked.

GridMarginalJoin keeps its original statement, the genuine same hit
event and its original grid probability. At the proof boundary:
- First transport the whole NNRat probability, rather than changing
  its type by mod_cast and asking defeq to match a new real conditional
  sum. Prove equality of those sums elementwise using the exact
  residue_root iff in the two Decidable-agnostic proof branches.
- The type of hE deliberately uses the same Classical.propDecidable
  required by the already green union_bound ABI. No new event, changed
  residue, cutoff, normalization, or arithmetic bound.

Both raw log and source SHA checked. 129 peer Lean sources unchanged,
both import names and exact selected 39 order unchanged. No Lean,
hosted dispatch, GitHub write or source acceptance.
