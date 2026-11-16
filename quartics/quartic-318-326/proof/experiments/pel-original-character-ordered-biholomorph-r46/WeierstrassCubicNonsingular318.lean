module
public import WeierstrassActualCubicSurjectivity318
public import AnalyticSquaredDerivative318
public section
noncomputable section
namespace WeierstrassCubicNonsingular318
open Complex Filter Set AnalyticSquaredDerivative318
open scoped Topology
set_option maxHeartbeats 2200000
variable (P : PeriodPair)

/-- The actual lattice-sum cubic has no repeated finite root. Attainment
comes from the original Weierstrass map, and the local order contradiction
uses its original derivative and its original global meromorphic germ. -/
theorem no_multiple_root (e : ℂ) (hc : 4*e^3-P.g₂*e-P.g₃=0) :
    12*e^2-P.g₂≠0 := by
  intro hd
  obtain ⟨z,hz,he⟩ := WeierstrassActualCubicSurjectivity318.exists_value P e
  let f : ℂ → ℂ := fun w => P.weierstrassP w-e
  have hf : AnalyticAt ℂ f z := (P.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hh : AnalyticAt ℂ (fun w => 4*P.weierstrassP w+8*e) z := by
    exact (analyticAt_const.mul (P.analyticOnNhd_weierstrassP z hz)).add analyticAt_const
  have hder : deriv f=P.derivWeierstrassP := by
    funext w
    rw [f,deriv_sub_const,P.deriv_weierstrassP]
  have hloc : ∀ᶠ w in 𝓝 z,f w=0 := by
    apply locally_zero hf hh (by change P.weierstrassP z-e=0; rw [he,sub_self])
    filter_upwards [P.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    rw [hder]
    change (P.derivWeierstrassP w)^2=(P.weierstrassP w-e)^2*(4*P.weierstrassP w+8*e)
    have hp := P.derivWeierstrassP_sq w hw
    linear_combination hp + hc + (P.weierstrassP w-e)*hd
  obtain ⟨w,hw,hew⟩ := WeierstrassActualCubicSurjectivity318.exists_value P (e+1)
  have hconst : ∀ᶠ v in 𝓝 z,P.weierstrassP v=e := by
    filter_upwards [hloc] with v hv
    exact sub_eq_zero.mp hv
  have hv := meromorphic_value P.meromorphic_weierstrassP e hconst w
    (P.analyticOnNhd_weierstrassP w hw).continuousAt
  rw [hew] at hv
  have : (1:ℂ)=0 := by linear_combination hv
  exact one_ne_zero this

/-- Genuine nonzero discriminant of the actual period sums. No abstract
elliptic-curve nonsingularity premise is supplied. -/
theorem discriminant_ne_zero : P.g₂^3-27*P.g₃^2≠0 := by
  intro hΔ
  by_cases h2 : P.g₂=0
  · have h3 : P.g₃=0 := by
      have hs : P.g₃^2=0 := by rw [h2] at hΔ; linear_combination -(1/27:ℂ)*hΔ
      exact pow_eq_zero hs
    exact no_multiple_root P 0 (by simp [h2,h3]) (by simp [h2])
  · let e : ℂ := -3*P.g₃/(2*P.g₂)
    have he_mul : (12*e^2-P.g₂)*P.g₂^2= -(P.g₂^3-27*P.g₃^2) := by
      dsimp [e]
      field_simp [h2] <;> ring
    have he : 12*e^2-P.g₂=0 := by
      rw [hΔ,neg_zero] at he_mul
      exact (mul_eq_zero.mp he_mul).resolve_right (pow_ne_zero 2 h2)
    have hc_mul : (4*e^3-P.g₂*e-P.g₃)*(2*P.g₂^3)=P.g₃*(P.g₂^3-27*P.g₃^2) := by
      dsimp [e]
      field_simp [h2] <;> ring
    have hc : 4*e^3-P.g₂*e-P.g₃=0 := by
      rw [hΔ,mul_zero] at hc_mul
      exact (mul_eq_zero.mp hc_mul).resolve_right (mul_ne_zero (by norm_num) (pow_ne_zero 3 h2))
    exact no_multiple_root P e hc he

/-- At every actual affine cubic point at least one of its two partial
derivatives is nonzero, including all original branch points. -/
theorem affine_smooth (x y : ℂ) (hc : y^2=4*x^3-P.g₂*x-P.g₃) :
    2*y≠0 ∨ 12*x^2-P.g₂≠0 := by
  by_cases hy : y=0
  · right
    apply no_multiple_root P x
    simpa only [hy,zero_pow (by decide : 2≠0)] using hc.symm
  · left
    exact mul_ne_zero (by norm_num) hy
end WeierstrassCubicNonsingular318
