module
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.Tactic
public section
noncomputable section
open WeierstrassCurve

namespace SelectedShortOrdinaryRatio318
variable {R : Type*} [CommRing R]

private theorem unit_neg48 (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) :
    IsUnit (-48:R) := by
  convert ((h2.pow 4).mul h3).neg using 1 <;> norm_num

private theorem unit_neg864 (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) :
    IsUnit (-864:R) := by
  convert ((h2.pow 5).mul (h3.pow 3)).neg using 1 <;> norm_num

variable (W : WeierstrassCurve R) [W.IsShortNF] [W.IsElliptic]

theorem short_c4 : W.c₄ = -48*W.a₄ := by
  simp only [WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    a₁_of_isShortNF,a₂_of_isShortNF,a₃_of_isShortNF]
  ring

theorem short_c6 : W.c₆ = -864*W.a₆ := by
  simp only [WeierstrassCurve.c₆,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,
    a₁_of_isShortNF,a₂_of_isShortNF,a₃_of_isShortNF]
  ring

theorem c4_cube_j : W.c₄^3 = W.j*W.Δ := by
  change W.c₄^3 = ((↑W.Δ'⁻¹:R)*W.c₄^3)*(W.Δ' : R)
  rw [mul_right_comm (↑W.Δ'⁻¹:R),Units.inv_mul,one_mul]

theorem c6_sq_j : W.c₆^2 = (W.j-1728)*W.Δ := by
  calc
    _ = W.c₄^3-1728*W.Δ := by linear_combination W.c_relation
    _ = _ := by rw [c4_cube_j]; ring

/-- Units on the entire ordinary test ring; this is not a nonvanishing
argument valid only on fields. -/
theorem coeff4_unit (hj : IsUnit W.j) : IsUnit W.a₄ := by
  have h : IsUnit (W.c₄^3) := by
    rw [c4_cube_j]; exact hj.mul W.isUnit_Δ
  have hh := (isUnit_pow_iff (by decide : 3 ≠ 0)).mp h
  rw [short_c4] at hh
  exact (IsUnit.mul_iff.mp hh).2

theorem coeff6_unit (h1728 : IsUnit (W.j-1728)) : IsUnit W.a₆ := by
  have h : IsUnit (W.c₆^2) := by
    rw [c6_sq_j]; exact h1728.mul W.isUnit_Δ
  have hh := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp h
  rw [short_c6] at hh
  exact (IsUnit.mul_iff.mp hh).2

variable (V : WeierstrassCurve R) [V.IsShortNF] [V.IsElliptic]

/-- Equality of the actual j-invariants gives the two-coefficient
relation over the base ring, with cancellation only by known units. -/
theorem equal_j_cross (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j) :
    V.a₆^2*W.a₄^3 = W.a₆^2*V.a₄^3 := by
  have hi : V.c₆^2*W.c₄^3 = W.c₆^2*V.c₄^3 := by
    rw [c6_sq_j V,c4_cube_j W,c6_sq_j W,c4_cube_j V,← hj]
    ring
  rw [short_c4 W,short_c4 V,short_c6 W,short_c6 V] at hi
  apply (((unit_neg864 h2 h3).pow 2).mul ((unit_neg48 h2 h3).pow 3)).mul_left_cancel
  linear_combination hi

variable (hW0 : IsUnit W.j) (hW1 : IsUnit (W.j-1728))
variable (hV0 : IsUnit V.j) (hV1 : IsUnit (V.j-1728))

@[expose] def ratio4 : Rˣ := (coeff4_unit V hV0).unit * (coeff4_unit W hW0).unit⁻¹
@[expose] def ratio6 : Rˣ := (coeff6_unit V hV1).unit * (coeff6_unit W hW1).unit⁻¹

theorem ratio4_mul : (ratio4 W V hW0 hV0:R)*W.a₄ = V.a₄ := by
  have h : ratio4 W V hW0 hV0 * (coeff4_unit W hW0).unit = (coeff4_unit V hV0).unit := by
    simp [ratio4,mul_assoc]
  simpa only [Units.val_mul,IsUnit.unit_spec] using congrArg (fun u : Rˣ => (u:R)) h

theorem ratio6_mul : (ratio6 W V hW1 hV1:R)*W.a₆ = V.a₆ := by
  have h : ratio6 W V hW1 hV1 * (coeff6_unit W hW1).unit = (coeff6_unit V hV1).unit := by
    simp [ratio6,mul_assoc]
  simpa only [Units.val_mul,IsUnit.unit_spec] using congrArg (fun u : Rˣ => (u:R)) h

theorem equal_j_ratios (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j) :
    (ratio6 W V hW1 hV1)^2 = (ratio4 W V hW0 hV0)^3 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  apply (((coeff6_unit W hW1).pow 2).mul ((coeff4_unit W hW0).pow 3)).mul_right_cancel
  calc
    _ = ((ratio6 W V hW1 hV1:R)*W.a₆)^2*W.a₄^3 := by ring
    _ = V.a₆^2*W.a₄^3 := by rw [ratio6_mul]
    _ = W.a₆^2*V.a₄^3 := equal_j_cross W V h2 h3 hj
    _ = W.a₆^2*((ratio4 W V hW0 hV0:R)*W.a₄)^3 := by rw [ratio4_mul]
    _ = _ := by ring

/-- Actual square scale c=(a6 ratio)/(a4 ratio). A root of c gives
both fourth and sixth powers required for scaling the short models. -/
@[expose] def ratio : Rˣ := ratio6 W V hW1 hV1 * (ratio4 W V hW0 hV0)⁻¹

theorem ratio_sq (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j) :
    (ratio W V hW0 hW1 hV0 hV1)^2 = ratio4 W V hW0 hV0 := by
  calc
    _ = (ratio6 W V hW1 hV1)^2 * ((ratio4 W V hW0 hV0)^2)⁻¹ := by unfold ratio; group
    _ = _ := by rw [equal_j_ratios W V hW0 hW1 hV0 hV1 h2 h3 hj]; group

theorem ratio_cube (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : W.j = V.j) :
    (ratio W V hW0 hW1 hV0 hV1)^3 = ratio6 W V hW1 hV1 := by
  calc
    _ = ratio6 W V hW1 hV1 * (ratio6 W V hW1 hV1)^2 * ((ratio4 W V hW0 hV0)^3)⁻¹ := by
      unfold ratio; group
    _ = _ := by rw [equal_j_ratios W V hW0 hW1 hV0 hV1 h2 h3 hj,mul_assoc,mul_inv_cancel,mul_one]

end SelectedShortOrdinaryRatio318

#print axioms SelectedShortOrdinaryRatio318.equal_j_ratios
#print axioms SelectedShortOrdinaryRatio318.ratio_cube
