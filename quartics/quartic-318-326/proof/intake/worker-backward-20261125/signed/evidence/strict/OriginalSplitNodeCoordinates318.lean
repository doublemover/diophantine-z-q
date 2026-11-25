module
public import Mathlib.RingTheory.AdjoinRoot
public section
noncomputable section

namespace OriginalSplitNodeCoordinates318

open Polynomial

variable {R : Type*} [CommRing R]

/-- The split-node equation. This is the literal four-definition
coordinate presentation of SelectedJNodeHartogs318, without importing
that unrelated historical Hartogs proof. -/
@[expose] def equation (π : R) : R[X][X] := C (X : R[X])*X - C (C π)
abbrev Node (π : R) := AdjoinRoot (equation π)
abbrev xAxis (π : R) : Node π := AdjoinRoot.root _
abbrev yAxis (π : R) : Node π := AdjoinRoot.of (equation π) (X : R[X])

end OriginalSplitNodeCoordinates318
