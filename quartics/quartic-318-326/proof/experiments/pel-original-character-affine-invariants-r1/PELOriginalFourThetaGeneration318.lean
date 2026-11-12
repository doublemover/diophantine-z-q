module
public import PELOriginalThetaAddition318
public import PELOriginalLevelPowerSections318
public import PELOriginalSquareGeneration318
public section
noncomputable section
namespace PELOriginalFourThetaGeneration318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalThetaConvergence318 PELOriginalLevelTheta318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalThetaHermitianGauge318
open PELOriginalThetaGaugeMatrix318 PELOriginalSiegelNormalization318
variable (τ:ℂ) (hτ:0<τ.im)

lemma exists_product_nonzero (z:ComplexVectors):
    ∃a,theta τ (z+a)*theta τ (z-a)≠0:=by
  obtain ⟨p,hp⟩:=PELOriginalThetaConstantCoefficient318.exists_nonzero τ hτ
  apply EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero
    (fun a=>theta τ (z+a)) (fun a=>theta τ (z-a))
    ((PELOriginalThetaHolomorphy318.holomorphic τ hτ).comp
      (differentiable_const.add differentiable_id))
    ((PELOriginalThetaHolomorphy318.holomorphic τ hτ).comp
      (differentiable_const.sub differentiable_id))
  · refine ⟨p-z,?_⟩
    rw [show z+(p-z)=p by abel]
    exact hp
  · refine ⟨z-p,?_⟩
    simpa only [sub_sub_cancel] using hp

/-- The FOUR explicit level-two characteristic functions have no common
zero anywhere on the actual normalized covering C². This is obtained from
the proved infinite-series addition identity, not from independence alone. -/
theorem finite_coordinate_nonzero (z:ComplexVectors):
    ∃r:Label 2,levelTheta τ 2 r z≠0:=by
  obtain ⟨a,ha⟩:=exists_product_nonzero τ hτ z
  by_contra h
  push_neg at h
  apply ha
  rw [PELOriginalThetaAddition318.addition τ hτ]
  simp only [h,zero_mul,Finset.sum_const_zero]

/-- Four explicit global sections generate the square of the SAME
original polarization line at EVERY original quotient point. Their actual
full lattice factor, local charts, and nonzero gauge were constructed
previously. No point/tangent separation or embedding is inferred. -/
theorem four_sections_basepoint_free (q:Base τ):
    ∃r:Label 2,(PELOriginalLevelPowerSections318.levelSection τ hτ 2 r q).2≠0:=by
  let z:ComplexVectors:=chart τ hτ ((core τ hτ).indexAt q) q
  obtain ⟨r,hr⟩:=finite_coordinate_nonzero τ hτ (normalization τ hτ z)
  refine ⟨r,?_⟩
  change gauge (bilinearMap τ) (normalization τ hτ z)^2*
    levelTheta τ 2 r (normalization τ hτ z)≠0
  exact mul_ne_zero (pow_ne_zero _ (gauge_nonzero _ _)) hr
theorem evaluation_surjective (q:Base τ) (v:PowerFiber τ hτ 2 q):
    ∃r:Label 2,∃c:ℂ,c*(PELOriginalLevelPowerSections318.levelSection τ hτ 2 r q).2=v:=by
  obtain ⟨r,hr⟩:=four_sections_basepoint_free τ hτ q
  exact ⟨r,v/(PELOriginalLevelPowerSections318.levelSection τ hτ 2 r q).2,div_mul_cancel₀ v hr⟩
lemma exactly_four:Fintype.card (Label 2)=4:=by
  rw [label_card]
  norm_num
end PELOriginalFourThetaGeneration318
