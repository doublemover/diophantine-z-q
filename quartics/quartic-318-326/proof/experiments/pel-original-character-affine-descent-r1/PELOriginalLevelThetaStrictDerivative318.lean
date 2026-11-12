module
public import PELOriginalThetaContinuousDerivative318
public import PELOriginalLevelThreeTangentSeparation318
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public section
noncomputable section
namespace PELOriginalLevelThetaStrictDerivative318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalThetaHermitianGauge318 PELOriginalThetaGaugeMatrix318
open PELOriginalGaugedTheta318 PELOriginalSiegelNormalization318
open PELOriginalAllLevelHolomorphicMap318 ComplexProjectiveComplexAtlas318
variable (τ:ℂ) (hτ:0<τ.im)
lemma theta_contDiff_one (N:ℕ) [NeZero N] (r:Label N):
    ContDiff ℂ 1 (levelTheta τ N r):=
  PELOriginalThetaContinuousDerivative318.selected_contDiff_one τ hτ (1/(N:ℝ))
    (inverse_level_positive N) (accepts N r)
lemma normalized_contDiff_one (N:ℕ) [NeZero N] (r:Label N):
    ContDiff ℂ 1 (normalizedValue τ N r):=
  (((gauge_smooth τ).of_le (by simp)).pow N).mul (theta_contDiff_one τ hτ N r)
lemma value_contDiff_one (N:ℕ) [NeZero N] (r:Label N):
    ContDiff ℂ 1 (value τ hτ N r):=
  (normalized_contDiff_one τ hτ N r).comp
    (normalization τ hτ).toContinuousLinearEquiv.contDiff

/-- C¹ is proved for the literal actual chart ratio, on precisely the
open locus where its original denominator is nonzero. -/
lemma ratio_contDiffAt (n:ℕ) (j:Label (n+2)) (z:ComplexVectors)
    (hz:value τ hτ (n+2) j z≠0):
    ContDiffAt ℂ 1 (ratioVector τ hτ n j) z:=by
  have hd:ContDiffAt ℂ 1
      (fun w:ComplexVectors=>fun i:{i:Label (n+2)//i≠j}=>
        value τ hτ (n+2) i.val w/value τ hτ (n+2) j w) z:=by
    apply contDiffAt_pi.mpr
    intro i
    exact (value_contDiff_one τ hτ (n+2) i.val).contDiffAt.div
      (value_contDiff_one τ hτ (n+2) j).contDiffAt hz
  exact (coordinates (Label (n+2)) 0 j).toContinuousLinearEquiv.contDiff.contDiffAt.comp z hd

lemma ratio_hasStrictFDerivAt (n:ℕ) (j:Label (n+2)) (z:ComplexVectors)
    (hz:value τ hτ (n+2) j z≠0):
    HasStrictFDerivAt (ratioVector τ hτ n j)
      (fderiv ℂ (ratioVector τ hτ n j) z) z:=
  (ratio_contDiffAt τ hτ n j z hz).hasStrictFDerivAt (by norm_num)

/-- A strict, injective complex derivative in the independently defined
actual target chart. This is the inverse-function input, not merely a
pointwise formal derivative or a renamed immersion assumption. -/
theorem level_three_strict_injective (j:Label 3) (z:ComplexVectors)
    (hz:value τ hτ 3 j z≠0):
    HasStrictFDerivAt (ratioVector τ hτ 1 j)
      (fderiv ℂ (ratioVector τ hτ 1 j) z) z ∧
    Function.Injective (fderiv ℂ (ratioVector τ hτ 1 j) z):=
  ⟨ratio_hasStrictFDerivAt τ hτ 1 j z hz,
    PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ z j hz⟩
end PELOriginalLevelThetaStrictDerivative318
