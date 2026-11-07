module
public import ReciprocalDouble318
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Tactic
public section
namespace RegularCusp318
open WeierstrassCurve.Affine ReciprocalDouble318
variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- Vieta precludes two regular intersections and a singular reduction on
an integral cusp model. No reduction map or residue-field assertion is assumed. -/
theorem third_regular (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean (w ·))
    (D x₁ x₂ x₃ l n : F) (hD : w D<1) (h2 : w (2:F)≤1)
    (h1 : 1≤w x₁) (h2x : 1≤w x₂)
    (hs : x₁+x₂+x₃=l^2)
    (hp : x₁*x₂+x₂*x₃+x₃*x₁= -D-2*l*n)
    (hm : x₁*x₂*x₃=n^2) : 1≤w x₃ := by
  by_contra hn
  have hx3 : w x₃<1 := lt_of_not_ge hn
  have ha0 := apply_nonneg w x₁
  have hb0 := apply_nonneg w x₂
  have hc0 := apply_nonneg w x₃
  have hl0 := apply_nonneg w l
  have hn0 := apply_nonneg w n
  have he0 := apply_nonneg w (2:F)
  have hab0 : 0<w x₁*w x₂ := mul_pos (by linarith) (by linarith)
  have hab1 : 1≤w x₁*w x₂ := by nlinarith [mul_nonneg (show 0≤w x₁-1 by linarith) (show 0≤w x₂-1 by linarith)]
  have hc1 : w x₃<w x₁ := hx3.trans_le h1
  have hc2 : w x₃<w x₂ := hx3.trans_le h2x
  have hbc : w (x₂*x₃)<w (x₁*x₂) := by
    simp only [map_mul]
    nlinarith [mul_lt_mul_of_pos_left hc1 (show 0<w x₂ by linarith)]
  have hca : w (x₃*x₁)<w (x₁*x₂) := by
    simp only [map_mul]
    nlinarith [mul_lt_mul_of_pos_left hc2 (show 0<w x₁ by linarith)]
  have hsmall : w (x₂*x₃+x₃*x₁)<w (x₁*x₂) := (hna _ _).trans_lt (max_lt hbc hca)
  have hpair : w (x₁*x₂+x₂*x₃+x₃*x₁)=w x₁*w x₂ := by
    rw [add_assoc,hna.add_eq_left_of_lt (map_neg_eq_map w) hsmall,map_mul]
  have hl : w l^2≤max (w x₁) (w x₂) := by
    have hc : w x₃≤max (w x₁) (w x₂) := hc1.le.trans (le_max_left _ _)
    have hh := (hna (x₁+x₂) x₃).trans (max_le ((hna _ _)) hc)
    rw [hs] at hh
    change w (l^2)≤max (w x₁) (w x₂) at hh
    simpa only [map_pow] using hh
  have hm' : w n^2=w x₁*w x₂*w x₃ := by
    have hh := congrArg (fun x:F => w x) hm
    simpa only [map_mul,map_pow] using hh.symm
  have hln : w l^2*w x₃<w x₁*w x₂ := by
    rcases le_total (w x₁) (w x₂) with hh|hh
    · rw [max_eq_right hh] at hl
      exact (mul_le_mul_of_nonneg_right hl hc0).trans_lt (by nlinarith [mul_lt_mul_of_pos_left hc1 (show 0<w x₂ by linarith)])
    · rw [max_eq_left hh] at hl
      exact (mul_le_mul_of_nonneg_right hl hc0).trans_lt (mul_lt_mul_of_pos_left hc2 (show 0<w x₁ by linarith))
  have hln' : (w l*w n)^2<(w x₁*w x₂)^2 := by
    have hh := mul_lt_mul_of_pos_left hln hab0
    nlinarith [sq_nonneg (w l*w n)]
  have hln'' : w l*w n<w x₁*w x₂ := by nlinarith [mul_nonneg hl0 hn0]
  have hterm : w (2*l*n)<w x₁*w x₂ := by
    simp only [map_mul]
    have hh := mul_le_of_le_one_left (mul_nonneg hl0 hn0) h2
    nlinarith
  have hD' : w D<w x₁*w x₂ := hD.trans_le hab1
  have hright : w (-D-2*l*n)<w x₁*w x₂ := by
    simpa only [sub_eq_add_neg,map_neg_eq_map] using
      (hna (-D) (-(2*l*n))).trans_lt (max_lt (by simpa only [map_neg_eq_map] using hD') (by simpa only [map_neg_eq_map] using hterm))
  rw [←hp,hpair] at hright
  exact lt_irrefl _ hright

/-- Algebraic Vieta identities in the ordinary affine slope chart. -/
theorem slope_vieta (D x₁ y₁ x₂ y₂ l:F)
    (hc : y₁^2=x₁^3-D*x₁)
    (hl : l*(x₁-x₂)=y₁-y₂)
    (hs : l*(y₁+y₂)=x₁^2+x₁*x₂+x₂^2-D) :
    let x₃:=l^2-x₁-x₂
    let n:=y₁-l*x₁
    x₁+x₂+x₃=l^2 ∧
    x₁*x₂+x₂*x₃+x₃*x₁= -D-2*l*n ∧ x₁*x₂*x₃=n^2 := by
  dsimp
  have hp : x₁*x₂+x₂*(l^2-x₁-x₂)+(l^2-x₁-x₂)*x₁=
      -D-2*l*(y₁-l*x₁) := by
    linear_combination hs-l*hl
  refine ⟨by ring,hp,?_⟩
  linear_combination -hc+x₁*hp

theorem secant_slope_sym (D x₁ y₁ x₂ y₂ l:F)
    (hc₁ : y₁^2=x₁^3-D*x₁) (hc₂ : y₂^2=x₂^3-D*x₂)
    (hx : x₁≠x₂) (hl : l*(x₁-x₂)=y₁-y₂) :
    l*(y₁+y₂)=x₁^2+x₁*x₂+x₂^2-D := by
  apply (mul_left_cancel₀ (sub_ne_zero.mpr hx))
  linear_combination hc₁-hc₂+(y₁+y₂)*hl

end
end RegularCusp318
#print axioms RegularCusp318.third_regular
#print axioms RegularCusp318.slope_vieta
