module
public import PELOriginalSiegelNormalization318
public section
noncomputable section
namespace PELOriginalHermitianCoordinates318
open QuaternionicRealPeriod318 QuaternionicPeriodAlternating318
open PELQuaternionRealRepresentation318 PELPeriodRiemannForm318 PELOriginalHermitianForm318
variable (τ:ℂ) (hτ:0<τ.im)
/-- Exact scalar formula for the original Riemann form after its ACTUAL
period equivalence. The denominator is sqrt210*Im(tau), unchanged. -/
lemma riemann_coordinates (z w:ComplexVectors):
    riemann τ hτ z w=
      ((z 0).re*(w 0).im-(z 0).im*(w 0).re+
        (z 1).re*(w 1).im-(z 1).im*(w 1).re)/(alpha*τ.im):=by
  change -pairing ((periodEquiv τ hτ).symm z) ((periodEquiv τ hτ).symm w)=_
  rw [period_pairing τ hτ]
  have hz:period τ ((periodEquiv τ hτ).symm z)=z:=(periodEquiv τ hτ).apply_symm_apply z
  have hw:period τ ((periodEquiv τ hτ).symm w)=w:=(periodEquiv τ hτ).apply_symm_apply w
  rw [hz,hw]
  change -((_+_)/(alpha*τ.im))=_
  ring
/-- Full Hermitian form, not merely its diagonal or values on a basis. -/
lemma form_coordinates (z w:ComplexVectors):
    form τ hτ z w=(z 0*star (w 0)+z 1*star (w 1))/((alpha*τ.im:ℝ):ℂ):=by
  simp only [form,riemann_coordinates]
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im] <;>
    field_simp [alpha_pos.ne',hτ.ne'] <;> ring
end PELOriginalHermitianCoordinates318
