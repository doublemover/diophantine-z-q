module
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import ActualTwoDescentFieldMapNonzero318
public section
noncomputable section
namespace ActualTwoDescentFieldAlgebraicClosureHalving318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local instance : DecidableEq Qbar := Classical.decEq _

lemma rational_parameter_ne (n : F) (hn : n ≠ 0) : algebraMap F Qbar n ≠ 0 :=
  ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero (algebraMap F Qbar) hn

end ActualTwoDescentFieldAlgebraicClosureHalving318
