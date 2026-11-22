module
public import ActualGaussianWeberHenselianPointMap318
public section
noncomputable section

namespace ActualGaussianWeberQuarterTurn318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable {K : Type*} [Field K]

theorem turned_nonsingular (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1)
    {x y : K} (h : WeierstrassCurve.Affine.Nonsingular ((curve K).toAffine) x y) : WeierstrassCurve.Affine.Nonsingular ((curve K).toAffine) (-x) (i*y) := by
  apply nonsing_of_equation h2
  have he := (literal_equation x y).mp h.1
  linear_combination y^2 * hi - he

/-- The literal Weber automorphism, with a fixed choice of the root i.
This point function uses no externally supplied action or change of model. -/
@[expose] def turn (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1) : WP K → WP K
  | Point.zero => Point.zero
  | Point.some x y h => Point.some (-x) (i*y) (turned_nonsingular h2 i hi h)

theorem turn_some (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1)
    {x y : K} (h : WeierstrassCurve.Affine.Nonsingular ((curve K).toAffine) x y) :
    turn h2 i hi (Point.some x y h) =
      Point.some (-x) (i*y) (turned_nonsingular h2 i hi h) := rfl

theorem some_transport {x y x' y' : K}
    {h : WeierstrassCurve.Affine.Nonsingular ((curve K).toAffine) x y} {h' : WeierstrassCurve.Affine.Nonsingular ((curve K).toAffine) x' y'}
    (hx : x=x') (hy : y=y') :
    Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

variable (V : ValuationSubring K)

theorem chosen_square_generic (i : V) (hi : i^2 = -1) :
    (V.subtype i)^2 = (-1:K) := by
  simpa only [map_pow,map_neg,map_one] using congrArg V.subtype hi

theorem chosen_square_residue (i : V) (hi : i^2 = -1) :
    (residue V i)^2 = (-1:ResidueField V) := by
  simpa only [map_pow,map_neg,map_one] using congrArg (residue V) hi

/-- Specialize at the same valuation ring; on the right use exactly
the residue of the chosen root, not an independent square root.
No additivity or Henselian hypothesis is needed for this coordinate identity. -/
theorem specialize_turn (hK : (2:K) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (i : V) (hi : i^2 = -1) (P : WP K) :
    specialize V h2 (turn hK (V.subtype i) (chosen_square_generic V i hi) P) =
      turn h2 (residue V i) (chosen_square_residue V i hi) (specialize V h2 P) := by
  classical
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x ∈ V
    · have hnx : -x ∈ V := neg_mem hx
      let a : V := ⟨x,hx⟩
      let b : V := ⟨y,integral_y V ((literal_equation x y).mp h.1) hx⟩
      have ha : (⟨-x,hnx⟩ : V) = -a := Subtype.ext rfl
      have hb (hy : V.subtype i*y ∈ V) : (⟨V.subtype i*y,hy⟩ : V) = i*b :=
        Subtype.ext rfl
      simp only [turn_some,specialize,dif_pos hx,dif_pos hnx,finiteReduction]
      exact some_transport (by rw [ha,map_neg] <;> rfl) (by rw [hb,map_mul] <;> rfl)
    · have hnx : -x ∉ V := fun hn => hx (by simpa only [neg_neg] using neg_mem hn)
      simp only [turn_some,specialize,dif_neg hx,dif_neg hnx,turn]

end ActualGaussianWeberQuarterTurn318
