module
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Homeomorph.Lemmas
public section
noncomputable section
namespace StandardCellCoordinates318
open Set Metric

@[expose] def one : (Fin 1 → ℝ) ≃ₜ ℝ where
  toFun x := x 0
  invFun t := fun _ => t
  left_inv x := by funext i; have hi : i=0 := Subsingleton.elim _ _; rw [hi]
  right_inv t := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi (fun _ => continuous_id)

@[expose] def two : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ where
  toFun x := (x 0,x 1)
  invFun p := ![p.1,p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

theorem one_norm (x : Fin 1 → ℝ) : ‖one x‖=‖x‖ := by
  have hx : x=fun _ => x 0 := by funext i; have hi : i=0 := Subsingleton.elim _ _; rw [hi]
  change ‖x 0‖=‖x‖
  conv_rhs => rw [hx]
  rw [pi_norm_const]

theorem two_norm (x : Fin 2 → ℝ) : ‖two x‖=‖x‖ := by
  change max ‖x 0‖ ‖x 1‖=‖x‖
  apply le_antisymm
  · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg (x 0)) (le_max_left _ _))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem one_ball (x : Fin 1 → ℝ) : x∈ball 0 1 ↔ one x∈Ioo (-1:ℝ) 1 := by
  simp only [Metric.mem_ball,dist_zero_right,←one_norm,Real.norm_eq_abs,abs_lt,Set.mem_Ioo]

theorem one_closedBall (x : Fin 1 → ℝ) : x∈closedBall 0 1 ↔ one x∈Icc (-1:ℝ) 1 := by
  simp only [Metric.mem_closedBall,dist_zero_right,←one_norm,Real.norm_eq_abs,abs_le,Set.mem_Icc]

theorem two_ball (x : Fin 2 → ℝ) : x∈ball 0 1 ↔ two x∈ball 0 1 := by
  simp only [Metric.mem_ball,dist_zero_right,two_norm]

theorem two_closedBall (x : Fin 2 → ℝ) : x∈closedBall 0 1 ↔ two x∈closedBall 0 1 := by
  simp only [Metric.mem_closedBall,dist_zero_right,two_norm]

theorem one_sphere (x : Fin 1 → ℝ) (hx : x∈sphere 0 1) : one x=-1 ∨ one x=1 := by
  have hn : |one x|=1 := by simpa only [Metric.mem_sphere,dist_zero_right,←one_norm,Real.norm_eq_abs] using hx
  rcases le_total 0 (one x) with hp | hn'
  · right; rwa [abs_of_nonneg hp] at hn
  · left; rw [abs_of_nonpos hn'] at hn; linarith

theorem two_sphere (x : Fin 2 → ℝ) : x∈sphere 0 1 ↔ two x∈sphere 0 1 := by
  simp only [Metric.mem_sphere,dist_zero_right,two_norm]

@[expose] def oneOpen : ball (0:Fin 1 → ℝ) 1 ≃ₜ Ioo (-1:ℝ) 1 := one.subtype one_ball
@[expose] def oneClosed : closedBall (0:Fin 1 → ℝ) 1 ≃ₜ Icc (-1:ℝ) 1 := one.subtype one_closedBall
@[expose] def twoOpen : ball (0:Fin 2 → ℝ) 1 ≃ₜ ball (0:ℝ × ℝ) 1 := two.subtype two_ball
@[expose] def twoClosed : closedBall (0:Fin 2 → ℝ) 1 ≃ₜ closedBall (0:ℝ × ℝ) 1 := two.subtype two_closedBall
end StandardCellCoordinates318
