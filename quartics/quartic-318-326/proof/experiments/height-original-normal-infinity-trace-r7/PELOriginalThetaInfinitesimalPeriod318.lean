module
public import PELOriginalInfinitesimalLatticeCharacter318
public import PELOriginalThetaTranslationPeriod318
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public section
noncomputable section
namespace PELOriginalThetaInfinitesimalPeriod318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationSemicharacter318
open PELPeriodRiemannForm318
variable (τ:ℂ)(hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

lemma factor_hasFDerivAt(l:L τ hτ)(z:ComplexVectors):
    HasFDerivAt (factor τ hτ l)
      ((factor τ hτ l z*(Real.pi:ℂ)) • continuousLinear τ hτ l.val) z:=by
  have h:=((continuousLinear τ hτ l.val).hasFDerivAt (x:=z)).const_mul (Real.pi:ℂ)
  have he:=h.add_const ((Real.pi:ℂ)*form τ hτ l.val l.val/2+
    (Real.pi:ℂ)*Complex.I*(quadratic ((latticeEquiv τ hτ).symm l):ℂ))
  have he':HasFDerivAt (exponent τ hτ l)
      ((Real.pi:ℂ) • continuousLinear τ hτ l.val) z:=by
    apply he.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w=>by
      simp only [exponent,continuousLinear,linear]
      ring)
  have hx:=(Complex.hasDerivAt_exp _).comp_hasFDerivAt z he'
  convert hx using 1
  ext v
  simp only [factor,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

/-- The actual full derivative transforms by differentiating the SAME
Appell-Humbert identity, with its inhomogeneous Hermitian term retained. -/
lemma derivative_automorphy(l:L τ hτ)(z v:ComplexVectors):
    fderiv ℂ F (z+l.val) v=factor τ hτ l z*
      (fderiv ℂ F z v+(Real.pi:ℂ)*form τ hτ v l.val*F z):=by
  have hl:HasFDerivAt (fun w:ComplexVectors=>F (w+l.val))
      (fderiv ℂ F (z+l.val)) z:=by
    simpa only [ContinuousLinearMap.comp_id] using
      (PELOriginalGaugedTheta318.holomorphic τ hτ (z+l.val)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).add_const l.val)
  have hr:=(factor_hasFDerivAt τ hτ l z).mul
    (PELOriginalGaugedTheta318.holomorphic τ hτ z).hasFDerivAt
  have he:(fun w:ComplexVectors=>F (w+l.val))=
      fun w=>factor τ hτ l w*F w:=funext (PELOriginalGaugedTheta318.original_automorphy τ hτ l)
  rw [he] at hl
  have hd:=hl.unique hr
  have hv:=congrArg (fun A:ComplexVectors→L[ℂ]ℂ=>A v) hd
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    continuousLinear,linear] at hv
  linear_combination hv

/-- An affine-linear logarithmic directional derivative of the actual
original theta forces its exact infinitesimal lattice character. This
uses one produced nonzero value, not a global logarithm of theta. -/
lemma exact_character(v:ComplexVectors)(c:ℂ)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (hd:∀a,fderiv ℂ F a v=(c+ℓ a)*F a)(l:L τ hτ):
    ℓ l.val=(Real.pi:ℂ)*form τ hτ v l.val:=by
  obtain ⟨z,hz⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  have he:=derivative_automorphy τ hτ l z v
  rw [hd,hd,PELOriginalGaugedTheta318.original_automorphy,map_add] at he
  have hn:factor τ hτ l z*F z≠0:=mul_ne_zero (nonzero τ hτ l z) hz
  apply mul_left_cancel₀ hn
  linear_combination he

/-- Final actual tangent conclusion for the separately constructed
infinitesimal triple-product rigidity producer. Positivity on the original
carrier and its full lattice force the tangent vector itself to be zero. -/
theorem direction_zero(v:ComplexVectors)(c:ℂ)(ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (hd:∀a,fderiv ℂ F a v=(c+ℓ a)*F a):v=0:=
  PELOriginalInfinitesimalLatticeCharacter318.tangent_zero τ hτ v ℓ
    (exact_character τ hτ v c ℓ hd)
end PELOriginalThetaInfinitesimalPeriod318
