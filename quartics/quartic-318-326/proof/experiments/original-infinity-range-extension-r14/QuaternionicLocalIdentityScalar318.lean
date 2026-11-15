module
public import PELOriginalPrimeBaseInvolutions318
public section
noncomputable section
namespace QuaternionicLocalIdentityScalar318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicFixedParameter318
open QuaternionicPositiveDeterminant318 PELInertiaArithmeticFixedPoints318
open Filter Topology
set_option maxHeartbeats 1600000

/-- A fixed upper-half-plane Möbius germ with derivative one is scalar.
This uses the full original matrix, including its positive determinant. -/
theorem scalar_of_identity_derivative (M : RealMatrices) (hM : 0<M.det)
    (τ : ℂ) (hτ : 0<τ.im) (hfix : mobius M τ=τ)
    (hid : HasDerivAt (mobius M) 1 τ) : M=M 1 1 • (1:RealMatrices) := by
  have hd := QuaternionicPositiveDeterminant318.denominator_nonzero M hM τ hτ
  have hf := fractional_derivative (M 0 0:ℂ) (M 0 1:ℂ) (M 1 0:ℂ) (M 1 1:ℂ) τ hd
  have hdv : HasDerivAt (mobius M) ((M.det:ℂ)/(denominator M τ)^2) τ := by
    convert hf using 1 <;> simp only [Matrix.det_fin_two,Complex.ofReal_sub,Complex.ofReal_mul]
  have he := hdv.unique hid
  have hs : (denominator M τ)^2=(M.det:ℂ) := by
    have hh := (div_eq_iff (pow_ne_zero 2 hd)).mp he
    simpa only [one_mul] using hh.symm
  have hr := congrArg Complex.re hs
  have hline := fixesLine_of_mobius M τ hd hfix
  have hsq := determinant_squares M τ hτ hline
  have hr' : (M 1 0*τ.re+M 1 1)^2-(M 1 0*τ.im)^2=M.det := by
    simpa only [denominator,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,mul_zero,
      sub_zero] using hr
  have hc : M 1 0*τ.im=0 := by
    nlinarith [sq_nonneg (M 1 0*τ.im)]
  have hc0 : M 1 0=0 := (mul_eq_zero.mp hc).resolve_right hτ.ne'
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ hline
  have ha0 : M 0 0=M 1 1 := by simpa only [hc0,mul_zero,zero_mul,add_zero] using ha
  have hb0 : M 0 1=0 := by simpa only [hc0,neg_zero,zero_mul] using hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,Matrix.one_apply,ha0,hb0,hc0]

/-- Eventual equality is genuinely at the ambient complex point, so the
identity derivative is not inferred merely from equality on a thin set. -/
theorem scalar_of_local_identity (M : RealMatrices) (hM : 0<M.det) (τ : ℂ) (hτ : 0<τ.im)
    (h : mobius M =ᶠ[𝓝 τ] id) : M=M 1 1 • (1:RealMatrices) :=
  scalar_of_identity_derivative M hM τ hτ h.eq_of_nhds
    ((hasDerivAt_id τ).congr_of_eventuallyEq h)
end QuaternionicLocalIdentityScalar318
