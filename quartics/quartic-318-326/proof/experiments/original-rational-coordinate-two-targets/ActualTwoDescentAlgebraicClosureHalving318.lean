module
public import ActualTwoDescentActualEllipticFieldMap318
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public section
noncomputable section
namespace ActualTwoDescentAlgebraicClosureHalving318
abbrev Qbar := AlgebraicClosure ℚ
abbrev GalQ := Field.absoluteGaloisGroup ℚ
local instance : DecidableEq Qbar := Classical.decEq _

lemma rational_parameter_ne (n : ℚ) (hn : n ≠ 0) : algebraMap ℚ Qbar n ≠ 0 :=
  ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero (algebraMap ℚ Qbar) hn

end ActualTwoDescentAlgebraicClosureHalving318
