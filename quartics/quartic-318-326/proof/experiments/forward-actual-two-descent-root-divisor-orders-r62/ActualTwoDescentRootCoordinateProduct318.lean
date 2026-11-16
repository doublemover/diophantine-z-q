module
public import ActualTwoDescentSimpleRootCoordinates318
public section
noncomputable section
namespace ActualTwoDescentRootCoordinateProduct318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentAdjustedChordSquares318
open ActualTwoDescentSimpleRootCoordinates318 ActualTwoDescentChordPolynomial318
variable [DecidableEq K]

/-- The actual group-law product is a nonzero square at every simple root,
including infinity, inverse pairs and finite two-torsion intersections. -/
theorem actual_root_product_square {n : K} (R : SimpleRoot n) (P Q : Point n) :
    ∃ s : K, s ≠ 0 ∧ rootCoordinate R P*rootCoordinate R Q*rootCoordinate R (P+Q)=s^2 := by
  cases P with
  | zero =>
    refine ⟨rootCoordinate R Q,root_coordinate_nonzero R Q,?_⟩
    simp only [zero_add,rootCoordinate,one_mul]
    ring
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      refine ⟨rootCoordinate R (.some x₁ y₁ h₁),root_coordinate_nonzero R _,?_⟩
      simp only [add_zero,rootCoordinate,mul_one]
      ring
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂
      · obtain ⟨hx,hy⟩ := hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
        refine ⟨rootCoordinate R (.some x₁ y₁ h₁),root_coordinate_nonzero R _,?_⟩
        simp only [rootCoordinate,mul_one]
        rw [hx]
        ring
      · have H := actual_chord_polynomial n x₁ y₁ x₂ y₂ h₁.left h₂.left hxy
        dsimp only at H
        have hv := actual_chord_value n x₁ y₁ _ x₁ x₂ _ R.root H R.equation
        have hd := actual_chord_derivative n x₁ y₁ _ x₁ x₂ _ R.root H
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        exact actual_adjusted_chord_square (rootDerivative R) (x₁-R.root) (x₂-R.root)
          (_-R.root) _ _ R.simple hv hd

end ActualTwoDescentRootCoordinateProduct318
