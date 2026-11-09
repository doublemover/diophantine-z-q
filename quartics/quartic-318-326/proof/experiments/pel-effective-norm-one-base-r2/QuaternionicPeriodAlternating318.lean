module
public import QuaternionicRealPeriod318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public section
noncomputable section
namespace QuaternionicPeriodAlternating318
open QuaternionicRealPeriod318
set_option maxHeartbeats 900000
@[expose] def scale : ℝ := Real.sqrt 210
theorem scale_pos : 0<scale := Real.sqrt_pos.mpr (by norm_num)

/-- The fixed μ-oriented trace pairing in split-real matrix coordinates. Its
negative, not this form, has the standard E(v,Jv)>0 period orientation. -/
@[expose] def pairing (M N : RealMatrices) : ℝ :=
  ((M 0 0*N 0 1-M 0 1*N 0 0)+(M 1 0*N 1 1-M 1 1*N 1 0))/scale
@[expose] def oriented (M N : RealMatrices) : ℝ := -pairing M N
@[expose] def energy (z : ComplexVectors) : ℝ :=
  ((z 0).re^2+(z 0).im^2)+((z 1).re^2+(z 1).im^2)

theorem period_pairing (τ : ℂ) (hτ : 0<τ.im) (M N : RealMatrices) :
    pairing M N=
      (((period τ M 0).im*(period τ N 0).re-(period τ M 0).re*(period τ N 0).im)+
       ((period τ M 1).im*(period τ N 1).re-(period τ M 1).re*(period τ N 1).im)) /
        (scale*τ.im) := by
  simp only [pairing,period,row,LinearMap.coe_mk,AddHom.coe_mk,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  field_simp [scale_pos.ne',hτ.ne']
  <;> ring

theorem complexStructure_pairing (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) :
    oriented M (complexStructure τ hτ M)=energy (period τ M)/(scale*τ.im) := by
  rw [oriented,period_pairing τ hτ,period_complexStructure]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add,energy]
  ring

theorem energy_pos (z : ComplexVectors) (hz : z≠0) : 0<energy z := by
  have h0 := sq_nonneg (z 0).re
  have h1 := sq_nonneg (z 0).im
  have h2 := sq_nonneg (z 1).re
  have h3 := sq_nonneg (z 1).im
  have hn : 0≤energy z := by unfold energy; positivity
  apply lt_of_le_of_ne hn
  intro h
  have he : energy z=0 := h.symm
  have hz0re : (z 0).re=0 := by unfold energy at he; nlinarith
  have hz0im : (z 0).im=0 := by unfold energy at he; nlinarith
  have hz1re : (z 1).re=0 := by unfold energy at he; nlinarith
  have hz1im : (z 1).im=0 := by unfold energy at he; nlinarith
  apply hz
  funext i
  fin_cases i
  · exact Complex.ext (by simpa using hz0re) (by simpa using hz0im)
  · exact Complex.ext (by simpa using hz1re) (by simpa using hz1im)

/-- Genuine strict positivity for the SAME transported complex structure,
with the orientation sign recorded explicitly. -/
theorem oriented_positive (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) (hM : M≠0) :
    0<oriented M (complexStructure τ hτ M) := by
  rw [complexStructure_pairing]
  apply div_pos (energy_pos _ ?_) (mul_pos scale_pos hτ)
  intro h
  apply hM
  apply (periodEquiv τ hτ).injective
  simpa only [map_zero] using h

theorem original_negative (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) (hM : M≠0) :
    pairing M (complexStructure τ hτ M)<0 := by
  have h := oriented_positive τ hτ M hM
  change 0 < -pairing M (complexStructure τ hτ M) at h
  linarith

/-- Type(1,1) compatibility uses the actual Jτ, not merely Rosati positivity. -/
theorem complexStructure_invariant (τ : ℂ) (hτ : 0<τ.im) (M N : RealMatrices) :
    oriented (complexStructure τ hτ M) (complexStructure τ hτ N)=oriented M N := by
  simp only [oriented,period_pairing τ hτ,period_complexStructure,
    Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add]
  ring
end QuaternionicPeriodAlternating318
