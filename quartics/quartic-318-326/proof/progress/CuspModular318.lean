module
public import CuspLocation318
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.Periodic
public section
noncomputable section
namespace CuspModular318
open scoped MatrixGroups
open UpperHalfPlane Function
set_option maxHeartbeats 0

/-- Actual SL2(Z) action: a non-stabilizer cannot identify two high points. -/
theorem transformed_im_small (g:SL(2,ℤ)) (z:UpperHalfPlane)
    (hc:g 1 0≠0) (hz:3<z.im) : (g • z).im<(1:ℝ)/3 := by
  have hcz : (1:ℝ) ≤ |(g 1 0:ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hc2 : (1:ℝ)≤(g 1 0:ℝ)^2 := by
    have hs := sq_nonneg (|(g 1 0:ℝ)|-1)
    nlinarith [sq_abs (g 1 0:ℝ)]
  have hb := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g:GL (Fin 2) ℝ) z
  have hden : z.im^2≤Complex.normSq (denom (g:GL (Fin 2) ℝ) z) := by
    have hh : z.im^2≤((g 1 0:ℝ)*z.im)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im)]
    exact hh.trans hb
  rw [ModularGroup.im_smul_eq_div_normSq]
  apply (div_lt_iff₀ (UpperHalfPlane.normSq_denom_pos (g:GL (Fin 2) ℝ) z.im_ne_zero)).mpr
  nlinarith [sq_nonneg (z.im-3)]

/-- The exact norm of the actual cusp uniformizer supplies the inner radius. -/
theorem qParam_inner (m:ℝ) (hm:0<m) (z:UpperHalfPlane) (hz:10<z.im) :
    ‖Periodic.qParam m z‖≤CuspRadius318.inner m := by
  rw [Periodic.norm_qParam]
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff_of_pos_right hm).mpr
  change -2*Real.pi*z.im≤-20*Real.pi
  nlinarith [Real.pi_pos]

theorem qParam_power (m:ℕ) (hm:1≤m) (z:ℂ) :
    (Periodic.qParam (m:ℝ) z)^m=Periodic.qParam 1 z := by
  have hmC : (m:ℂ)≠0 := by exact_mod_cast (show m≠0 by omega)
  unfold Periodic.qParam
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- An actual q-coordinate disc at every selected complex lift has the
same level-uniform radius used by the Wronskian theorem. -/
theorem actual_cusp_disc (m N:ℝ) (hm:1≤m) (hN:m≤N)
    (z:UpperHalfPlane) (hz:10<z.im) :
    Real.exp (-21)/N≤CuspRadius318.radius m ∧
    ∀w:ℂ,‖w-Periodic.qParam m z‖≤CuspRadius318.radius m →
      ‖w‖<CuspRadius318.outer m := by
  refine ⟨CuspRadius318.radius_level_bound m N hm hN,?_⟩
  intro w hw
  apply CuspRadius318.centered_disc_inside m (by linarith) _ w _ hw
  exact qParam_inner m (by linarith) z hz

end CuspModular318
#print axioms CuspModular318.transformed_im_small
#print axioms CuspModular318.qParam_inner
#print axioms CuspModular318.qParam_power
#print axioms CuspModular318.actual_cusp_disc
