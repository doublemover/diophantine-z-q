# Actual DVR completion and formal contact map

Three modules, 27 exhaustive recursive declarations, strict Lean kernel replay and standard axioms only.

`SeparatedPrincipalLocal318` first proves actual unit-times-parameter-power decomposition in a separated local ring whose maximal ideal is principal. Nonvanishing of all parameter powers then proves that ring is a domain. A separate least-exponent argument proves every ideal principal. Neither domain nor Noetherianity is supplied to these generic conclusions.

`ActualDVRCompletion318` applies those constructions to Mathlib's actual `AdicCompletion (maximalIdeal R) R` for an actual DVR R. It proves the canonical completion map injective, computes the completed maximal ideal, and derives that the completion is itself a DVR. Completeness at its actual maximal ideal is obtained from the actual adic-completion API. The mapped uniformizer is irreducible, and the canonical additive valuation of every mapped element is exactly preserved, including zero.

The actual completion now supplies both target and completeness for the positive-even-contact formal evaluation. Any coefficient map A→R yields a genuine A[[S]]→R-hat sending S to the mapped u*pi^(2m), with all constant values proved. The contact exponent must be positive; no arbitrary formal evaluation at a unit is asserted.

`CompletionDescent318` derives faithful flatness of the actual completion map from actual adic-completion flatness and locality. Its residue equivalence is the canonical residue-field map, with its element formula proved.

Remaining scope: realization of source local rings as DVRs, the actual source coefficient map/formal quotient, and the geometric comparison with the source cover are not constructed here. This packet removes the previously supplied abstract completion/domain/DVR/valuation/faithful-flat inputs; it is not the full global geometric realization.

Replay `bash run.sh`. The pinned genuine Mathlib sources are used; no generated compiler object is a deliverable.
