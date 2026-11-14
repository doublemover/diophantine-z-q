module
public import PELOriginalThetaDirectionalHolomorphy318
public import PELOriginalGaugedTheta318
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public section
noncomputable section
namespace PELOriginalThetaDirectionalEntire318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaHolomorphy318
open PELOriginalThetaDirectionalHolomorphy318 PELOriginalGaugedTheta318
open PELOriginalThetaHermitianGauge318 PELOriginalThetaGaugeMatrix318
open PELOriginalSiegelNormalization318
variable (τ:ℂ)(hτ:0<τ.im)

/-- The actual gauge was independently constructed C-infinity; its
operator derivative is holomorphic by the precise C²-to-C¹ theorem,
not by an unsupported multivariable holomorphic-to-analytic shortcut. -/
lemma gauge_directional_entire(v:ComplexVectors):
    Differentiable ℂ (fun z=>fderiv ℂ (gauge (bilinearMap τ)) z v):=by
  have htwo:ContDiff ℂ (1+1) (gauge (bilinearMap τ)):=
    (gauge_smooth τ).of_le le_top
  have hone:ContDiff ℂ 1 (fderiv ℂ (gauge (bilinearMap τ))):=
    (contDiff_succ_iff_fderiv.mp htwo).2.2
  exact (evaluate v).differentiable.comp hone.differentiable_one

/-- Exact chain/product formula for the SAME original scalar theta,
retaining both the actual quadratic gauge and original normalization. -/
lemma actual_directional_formula(v z:ComplexVectors):
    fderiv ℂ (PELOriginalGaugedTheta318.value τ hτ) z v=
      gauge (bilinearMap τ) (normalization τ hτ z)*
        directionalTheta τ (normalization τ hτ v) (normalization τ hτ z)+
      theta τ (normalization τ hτ z)*
        fderiv ℂ (gauge (bilinearMap τ)) (normalization τ hτ z)
          (normalization τ hτ v):=by
  have hg:=((gauge_smooth τ).differentiable (by simp) (normalization τ hτ z)).hasFDerivAt
  have ht:=(PELOriginalThetaHolomorphy318.holomorphic τ hτ (normalization τ hτ z)).hasFDerivAt
  have hc:=(hg.mul ht).comp z
    ((normalization τ hτ).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt (x:=z))
  change HasFDerivAt (PELOriginalGaugedTheta318.value τ hτ) _ z at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [PELOriginalThetaDirectionalHolomorphy318.actual_derivative τ hτ]

/-- Genuine entire directional derivative on the ORIGINAL two-complex-
dimensional carrier. The theta term uses a full second weighted Z²
Gaussian estimate; all gauge/normalization derivative terms are included. -/
theorem directional_holomorphic(v:ComplexVectors):
    Differentiable ℂ (fun a=>fderiv ℂ (PELOriginalGaugedTheta318.value τ hτ) a v):=by
  have hn: Differentiable ℂ (normalization τ hτ):=
    (normalization τ hτ).toContinuousLinearEquiv.differentiable
  have hg:=((gauge_smooth τ).differentiable (by simp)).comp hn
  have hd:=(PELOriginalThetaDirectionalHolomorphy318.directional_holomorphic τ hτ
    (normalization τ hτ v)).comp hn
  have ht:=(PELOriginalThetaHolomorphy318.holomorphic τ hτ).comp hn
  have hgd:=(gauge_directional_entire τ (normalization τ hτ v)).comp hn
  have he:(fun a=>fderiv ℂ (PELOriginalGaugedTheta318.value τ hτ) a v)=
      fun a=>gauge (bilinearMap τ) (normalization τ hτ a)*
        directionalTheta τ (normalization τ hτ v) (normalization τ hτ a)+
      theta τ (normalization τ hτ a)*
        fderiv ℂ (gauge (bilinearMap τ)) (normalization τ hτ a)
          (normalization τ hτ v):=funext (actual_directional_formula τ hτ v)
  rw [he]
  exact (hg.mul hd).add (ht.mul hgd)
end PELOriginalThetaDirectionalEntire318
