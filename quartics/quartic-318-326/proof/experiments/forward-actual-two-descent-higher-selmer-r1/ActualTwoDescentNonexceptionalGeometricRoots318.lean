module
public import ActualTwoDescentContinuousTorsionCoordinates318
public section
noncomputable section
namespace ActualTwoDescentNonexceptionalGeometricRoots318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentScalarSquareRoots318
open ActualTwoDescentHalvingRoots318 ActualTwoDescentTorsionSquarePairs318

/-- Actual nonzero geometric roots of the original nonexceptional rational point, with correct product sign. -/
theorem actual_nonexceptional_geometric_roots (n x y : ℚ)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    ∃ a b c : Qbar, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      a^2=algebraMap ℚ Qbar x ∧ b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n ∧
      c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n ∧ a*b*c= -algebraMap ℚ Qbar y := by
  have hx' := rational_parameter_ne x hx
  have hB' : algebraMap ℚ Qbar x-algebraMap ℚ Qbar n ≠ 0 := by simpa only [map_sub] using rational_parameter_ne (x-n) hB
  have hA' : algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n ≠ 0 := by
    simpa only [map_add,map_mul,map_ofNat] using rational_parameter_ne (x+3*n) hA
  have hc' := ActualTwoDescentEllipticFieldCoordinates318.actual_curve_equation_map (algebraMap ℚ Qbar) n x y hc
  have H : SquarePair (algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
      (algebraMap ℚ Qbar x-algebraMap ℚ Qbar n) 1 1 := by
    refine ⟨scalarRoot (Units.mk0 (x+3*n) hA),scalarRoot (Units.mk0 (x-n) hB),scalar_root_ne _,scalar_root_ne _,?_,?_⟩
    · simpa only [one_mul,Units.val_mk0,map_add,map_mul,map_ofNat] using (scalar_root_square (Units.mk0 (x+3*n) hA)).symm
    · simpa only [one_mul,Units.val_mk0,map_sub] using (scalar_root_square (Units.mk0 (x-n) hB)).symm
  exact actual_halving_roots _ _ _ hx' hB' hA' hc' H

end ActualTwoDescentNonexceptionalGeometricRoots318
