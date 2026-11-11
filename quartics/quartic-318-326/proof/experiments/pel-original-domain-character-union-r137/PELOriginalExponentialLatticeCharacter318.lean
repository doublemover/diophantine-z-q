module
public import PELOriginalIntegralDualLattice318
public section
noncomputable section
namespace PELOriginalExponentialLatticeCharacter318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318 PELPeriodRiemannForm318
open PELOriginalIntegralDualLattice318
variable (τ:ℂ)(hτ:0<τ.im)
@[expose] def realPart(ℓ:ComplexVectors→ₗ[ℂ]ℂ):ComplexVectors→ₗ[ℝ]ℝ:=
  Complex.reCLM.toLinearMap.comp (ℓ.restrictScalars ℝ)

/-- The true lattice exponential identity first fixes the real part;
no logarithm branch or unjustified exponent cancellation is used. -/
lemma real_character(δ:ComplexVectors)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (he:∀l:L τ hτ,Complex.exp (ℓ l.val)=
      Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val))(l:L τ hτ):
    (ℓ l.val).re=Real.pi*(form τ hτ δ l.val).re:=by
  have hx:=Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (he l)
  obtain ⟨n,hn⟩:=Complex.exp_eq_one_iff.mp hx
  have hr:=congrArg Complex.re hn
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,sub_zero] at hr
  linarith

/-- Real-span agreement on the SAME whole lattice determines the full
complex-linear functional. Hermitian first-slot linearity is essential:
the conclusion is H(v,δ), not the conjugate-linear H(δ,v). -/
lemma identify_linear(δ:ComplexVectors)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (he:∀l:L τ hτ,Complex.exp (ℓ l.val)=
      Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)):
    ∀v,ℓ v=(Real.pi:ℂ)*form τ hτ v δ:=by
  have hmaps:realPart ℓ=Real.pi • realPart (linear τ hτ δ):=by
    apply linear_ext_lattice τ hτ
    intro l
    change (ℓ l.val).re=Real.pi*(form τ hτ l.val δ).re
    rw [hermitian τ hτ δ l.val]
    simpa only [Complex.star_def,Complex.conj_re] using real_character τ hτ δ ℓ he l
  have hr:∀v,(ℓ v).re=Real.pi*(form τ hτ v δ).re:=by
    intro v
    exact congrArg (fun f:ComplexVectors→ₗ[ℝ]ℝ=>f v) hmaps
  intro v
  apply Complex.ext
  · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hr v
  · have hi:=hr (Complex.I • v)
    simp only [map_smul,smul_eq_mul,form_smul,Complex.mul_re,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub] at hi
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    linarith

/-- Exact principal-lattice conclusion from the produced exponential
character. The imaginary discrepancy is an INTEGRAL 2πi multiple and
the already-proved perfect original pairing gives original period membership. -/
theorem period_of_character(δ:ComplexVectors)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (he:∀l:L τ hτ,Complex.exp (ℓ l.val)=
      Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)):
    δ∈L τ hτ:=by
  apply mem_of_integral_pairings τ hτ δ
  intro l
  have hx:=Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (he l)
  rw [identify_linear τ hτ δ ℓ he] at hx
  obtain ⟨n,hn⟩:=Complex.exp_eq_one_iff.mp hx
  refine ⟨n,?_⟩
  have hd:(Real.pi:ℂ)*form τ hτ l.val δ-(Real.pi:ℂ)*form τ hτ δ l.val=
      (2*(Real.pi:ℂ)*Complex.I)*(riemann τ hτ δ l.val:ℂ):=by
    have hs:=skew_difference τ hτ δ l.val
    linear_combination (Real.pi:ℂ)*hs
  rw [hd] at hn
  have hc:2*(Real.pi:ℂ)*Complex.I≠0:=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hi:(riemann τ hτ δ l.val:ℂ)=(n:ℂ):=by
    apply mul_left_cancel₀ hc
    exact hn.trans (mul_comm _ _)
  exact_mod_cast hi
end PELOriginalExponentialLatticeCharacter318
