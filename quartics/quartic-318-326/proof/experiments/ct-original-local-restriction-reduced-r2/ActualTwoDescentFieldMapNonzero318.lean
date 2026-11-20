module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public section
noncomputable section
namespace ActualTwoDescentSquareClassFieldMap318
variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [Field L] [CharZero L]

lemma field_map_ne_zero (f : K →+* L) {a : K} (ha : a ≠ 0) : f a ≠ 0 := by
  intro he
  apply ha
  apply f.injective
  simpa only [map_zero] using he

end ActualTwoDescentSquareClassFieldMap318
