module
public import RotatedWidths318
public import Mathlib.NumberTheory.Modular
public section
noncomputable section
open UpperHalfPlane Matrix
open scoped MatrixGroups
namespace RotatedStabilizer318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem conjugate_trace (g k:SL(2,ℤ)) :
    (g*k*g⁻¹) 0 0+(g*k*g⁻¹) 1 1=k 0 0+k 1 1 := by
  suffices hh:Matrix.trace (g*k*g⁻¹:SL(2,ℤ)).val=Matrix.trace k.val by
    simpa only [Matrix.trace_fin_two] using hh
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle,←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel]
  simp

/-- The conjugated stabilizer cannot contain the negative-unipotent branch:
its trace would be -2, contradicting Gamma1's actual level congruence. -/
theorem upper_triangular_translation (N:ℕ) (hN:5≤N) (g k:SL(2,ℤ))
    (hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 N) (hc:k 1 0=0) :
    k=ModularGroup.T^(k 0 1) := by
  have hd:k 0 0*k 1 1=1 := by
    have := k.det_coe
    rwa [Matrix.det_fin_two,hc,mul_zero,sub_zero] at this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · ext i j;fin_cases i <;>fin_cases j <;>
      simp [ha,hd,hc,ModularGroup.coe_T_zpow]
  · have ht := GammaOneFree318.trace_congruence N _ hk
    rw [conjugate_trace,ha,hd] at ht
    have hz:2-((-1:ℤ)+(-1))=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by norm_num) (by omega) ht
    norm_num at hz

/-- Two points above height1 cannot be identified by a matrix with nonzero
lower-left entry. This is the genuine modular action, not a supplied cusp model. -/
theorem lower_left_zero_of_high (k:SL(2,ℤ)) (tau:UpperHalfPlane)
    (ht:1<tau.im) (hk:1<(k•tau).im) : k 1 0=0 := by
  by_contra hc
  have hc2:(1:ℝ)≤(k 1 0:ℝ)^2 := by
    exact_mod_cast (one_le_sq_iff_one_le_abs (k 1 0)).mpr (Int.one_le_abs hc)
  have hn:Complex.normSq (UpperHalfPlane.denom k tau)=
      ((k 1 0:ℝ)*tau.re+(k 1 1:ℝ))^2+(k 1 0:ℝ)^2*tau.im^2 := by
    simp [ModularGroup.denom_apply,Complex.normSq_apply]
    ring
  have hden:0<Complex.normSq (UpperHalfPlane.denom k tau) := by
    rw [hn]
    nlinarith [sq_nonneg ((k 1 0:ℝ)*tau.re+(k 1 1:ℝ)),sq_nonneg tau.im]
  rw [ModularGroup.im_smul_eq_div_normSq] at hk
  have hsmall:Complex.normSq (UpperHalfPlane.denom k tau)<tau.im := by
    simpa only [one_mul] using (lt_div_iff₀ hden).mp hk
  rw [hn] at hsmall
  nlinarith [sq_nonneg ((k 1 0:ℝ)*tau.re+(k 1 1:ℝ)),sq_nonneg (tau.im-1)]

theorem high_translation (N:ℕ) (hN:5≤N) (g k:SL(2,ℤ))
    (hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 N) (tau:UpperHalfPlane)
    (ht:1<tau.im) (hkt:1<(k•tau).im) :
    ∃n:ℤ,k=ModularGroup.T^n ∧ (RotatedWidths318.width N (by omega) g:ℤ)∣n := by
  have he:=upper_triangular_translation N hN g k hk (lower_left_zero_of_high k tau ht hkt)
  refine ⟨k 0 1,he,?_⟩
  exact (RotatedWidths318.period_iff N (by omega) g _).mp (he ▸ hk)

end RotatedStabilizer318
