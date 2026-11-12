module
public import ActualTwoDescentDoublingCoordinates318
public section
noncomputable section
namespace ActualTwoDescentIdentityClassKernel318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentIdentityClassHalving318 ActualTwoDescentDoublingCoordinates318
variable [DecidableEq K]

/-- The kernel statement uses the actual elliptic doubling operation. -/
theorem actual_identity_class_iff_double (n x y : K) (hn : n ≠ 0)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    SquarePair (x+3*n) (x-n) 1 1 ↔ ∃ Q : Point n, Q+Q=point n x y hn hc := by
  constructor
  · intro H
    obtain ⟨Q,hQ,h⟩ := actual_identity_class_half n x y hn hx hB hA hc H
    exact ⟨Q,h⟩
  · rintro ⟨Q,hQ⟩
    cases Q with
    | zero =>
      have hz : (0 : Point n)=point n x y hn hc := by simpa using hQ
      exact False.elim (point_ne_zero n x y hn hc hz.symm)
    | some X Y hXY =>
      have hy : Y ≠ (curve n).toAffine.negY X Y := by
        intro he
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq he] at hQ
        exact point_ne_zero n x y hn hc hQ.symm
      have hY : Y ≠ 0 := by
        intro he
        apply hy
        rw [he,curve_negY]
        ring
      have hcurve : Y^2=X*(X-n)*(X+3*n) :=
        (curve_equation n X Y).mp hXY.left
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy] at hQ
      have hX : (curve n).toAffine.addX X X ((curve n).toAffine.slope X X Y Y)=x := by
        unfold point at hQ
        injection hQ
      rw [actual_addX_double n X Y hY] at hX
      have H := actual_double_identity_class n X Y hY hcurve
        (by simpa only [hX] using hB) (by simpa only [hX] using hA)
      simpa only [hX] using H

end ActualTwoDescentIdentityClassKernel318
