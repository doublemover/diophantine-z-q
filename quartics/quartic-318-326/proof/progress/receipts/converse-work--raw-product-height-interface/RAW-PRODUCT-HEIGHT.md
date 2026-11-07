# Literal root product and maximum-index height bridge

Status: COMPLETE. Three modules and sixteen declarations, standard axioms only. The final theorem assumes only the literal source constraints. All finite-place, actual global-label, canonical-height, and height-normalization inputs are discharged by their checked producers. This packet does not assume an abstract height or canonical-height oracle.

## Exact objects and results

- `Kprod w` is the literal source field element `pair (w 143) (w 144)`.
- `source_product` derives `Kprod w = product_i root(w,i)` from the six exact residuals at indices 100 through 105 of `stage0 S`. It does not derive this field identity from a norm equality.
- `root_square_eq_abscissa` consumes the actual `RawOddAnchorPoints318.RootLabels` point equalities. `source_squared_product` therefore identifies `Kprod²` with the product of the four actual abscissae `x(n_i P)`.
- `maxIndex labels` is the natural maximum of the four integer absolute values, implemented as `Finset.univ.sup natAbs`. The maximum is attained, bounds every label, and has no artificial lower cutoff.
- `max_index_sum_lower` specializes the existing actual `GlobalIndexHeight318.multiple_height_lower` to the fully constructed `ActualCanonicalHeight318.canonical_data`, selects an attained maximum, and bounds that summand by the sum using actual nonnegative absolute heights.
- `source_height_identity` applies the already checked normalized product-height identity. `RootLabels` ensures all labels are nonzero, so a separate oddness premise is unnecessary at this step. The exact finite-place input is: for every actual normalized finite place, all four abscissae have value at most one, or all have value at least one.
- `source_max_index_lower` concludes `B² - 6 < absLogHeight₁(Kprod²)`, with that finite-place input explicit.
- `scalar_abs_le_maxIndex_add_one` covers both literal source orientations `c=n_1-1` and `c=-n_1-1`. `three_le_maxIndex_of_scalar_bound` obtains the downstream condition `3≤B` from `4<|c|` without changing the maximum.

## Final unconditional assembly

`ActualRawProductHeight318.source_height_identity` and `source_max_index_lower` consume the now-checked `ActualOddProductHeight318.odd_multiple_height_product`, removing the finite-place input. At the anchor scale, `anchored_source_max_index_lower` also derives oddness directly from the source residuals and the actual root/scalar point labels.

`SourceMaxIndexHeight318.source_max_index_data` finally consumes the unconditional `ActualGlobalGenerator318.source_global_labels`. From the literal `Constraints (stage0 (3^65536)) w` alone it returns actual root labels and scalar label c, all labels odd, both possible source orientations, the existing bound `2^49151<|c|`, `|c|≤B+1`, `3≤B`, the exact identity `h(Kprod²)=sum_i h(x(n_iP))`, and the strict lower bound `B²-6<h(Kprod²)`.

The preliminary `RawProductHeight318` module preserves the explicit interface statements for reuse and independent auditing; the final two modules discharge them rather than changing their meaning. No mathematical premise beyond the original source constraints remains in `source_max_index_data`. This is a subresult of source soundness, not the final contradiction theorem.

## Replay

Run `bash converse-work/raw-product-height-interface/verify.sh` from the workspace root. It uses the pinned Lean 4.35.0 binary, the existing height-work Mathlib project, and the explicitly listed sibling module paths. Kernel checking is forced with `debug.skipKernelTC=false`; the script rejects errors or `sorryAx`. `receipt.json` binds sources, logs, compiled artifact, and interface inputs. No repository or live height-work files were edited.
