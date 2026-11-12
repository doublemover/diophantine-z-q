module
public import ActualTwoDescentFieldContinuousTorsionCoordinates318
public section
noncomputable section
namespace ActualTwoDescentFieldNonexceptionalGeometricRoots318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldScalarSquareRoots318
open ActualTwoDescentHalvingRoots318 ActualTwoDescentTorsionSquarePairs318

/-- Actual nonzero geometric roots of the original nonexceptional base-field point, with correct product sign. -/
theorem actual_nonexceptional_geometric_roots (n x y : F)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    ∃ a b c : Qbar, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      a^2=algebraMap F Qbar x ∧ b^2=algebraMap F Qbar x-algebraMap F Qbar n ∧
      c^2=algebraMap F Qbar x+3*algebraMap F Qbar n ∧ a*b*c= -algebraMap F Qbar y := by
  have hx' := rational_parameter_ne x hx
  have hB' : algebraMap F Qbar x-algebraMap F Qbar n ≠ 0 := by simpa only [map_sub] using rational_parameter_ne (x-n) hB
  have hA' : algebraMap F Qbar x+3*algebraMap F Qbar n ≠ 0 := by
    simpa only [map_add,map_mul,map_ofNat] using rational_parameter_ne (x+3*n) hA
  have hc' := ActualTwoDescentEllipticFieldCoordinates318.actual_curve_equation_map (algebraMap F Qbar) n x y hc
  have H : SquarePair (algebraMap F Qbar x+3*algebraMap F Qbar n)
      (algebraMap F Qbar x-algebraMap F Qbar n) 1 1 := by
    refine ⟨scalarRoot (Units.mk0 (x+3*n) hA),scalarRoot (Units.mk0 (x-n) hB),scalar_root_ne _,scalar_root_ne _,?_,?_⟩
    · simpa only [one_mul,Units.val_mk0,map_add,map_mul,map_ofNat] using (scalar_root_square (Units.mk0 (x+3*n) hA)).symm
    · simpa only [one_mul,Units.val_mk0,map_sub] using (scalar_root_square (Units.mk0 (x-n) hB)).symm
  exact actual_halving_roots _ _ _ hx' hB' hA' hc' H

end ActualTwoDescentFieldNonexceptionalGeometricRoots318
