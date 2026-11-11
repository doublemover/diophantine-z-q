module
public import PELOriginalExponentialLatticeCharacter318
public section
noncomputable section
namespace PELOriginalInfinitesimalLatticeCharacter318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318 PELPeriodRiemannForm318
open PELOriginalIntegralDualLattice318 PELOriginalExponentialLatticeCharacter318
open PELOriginalMetricSmoothCoefficient318
variable (τ:ℂ)(hτ:0<τ.im)

/-- The infinitesimal analogue has an EXACT equality, rather than an
integral exponential ambiguity. On the same full period lattice this
forces the original source tangent vector to vanish. -/
theorem tangent_zero(v:ComplexVectors)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (he:∀l:L τ hτ,ℓ l.val=(Real.pi:ℂ)*form τ hτ v l.val):v=0:=by
  have hexp:=fun l:L τ hτ=>congrArg Complex.exp (he l)
  have hid:=identify_linear τ hτ v ℓ hexp
  have hz:∀l:L τ hτ,riemann τ hτ v l.val=0:=by
    intro l
    have hh:=he l
    rw [hid] at hh
    have hp:(Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hs:form τ hτ l.val v=form τ hτ v l.val:=mul_left_cancel₀ hp hh
    have hd:=skew_difference τ hτ v l.val
    rw [hs,sub_self] at hd
    have hn:2*Complex.I≠0:=mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hc:(riemann τ hτ v l.val:ℂ)=0:=
      (mul_eq_zero.mp hd.symm).resolve_left hn
    exact Complex.ofReal_eq_zero.mp hc
  have hzero:secondLinear τ hτ v=0:=by
    apply linear_ext_lattice τ hτ
    intro l
    exact hz l
  by_contra hv
  have hp:=positive τ hτ v hv
  have heq:riemann τ hτ v (Complex.I • v)=0:=
    congrArg (fun f:ComplexVectors→ₗ[ℝ]ℝ=>f (Complex.I • v)) hzero
  rw [heq] at hp
  exact (lt_irrefl 0) hp
end PELOriginalInfinitesimalLatticeCharacter318
