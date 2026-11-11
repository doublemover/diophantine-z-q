module
public import PELOriginalProjectiveRatioKernel318
public import EntireDifferentiatedTriple318
public import PELOriginalThetaDirectionalEntire318
public import PELOriginalThetaInfinitesimalPeriod318
public section
noncomputable section
namespace PELOriginalLevelThreeTangentSeparation318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalAllLevelProjectiveMap318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalTripleDirectionalEvaluation318
variable (τ:ℂ)(hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=PELOriginalPeriodLattice318.original_discrete τ hτ
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- True vanishing of an original projective chart derivative produces
an affine logarithmic directional law on ALL of the original universal
carrier. Entire directional theta is supplied by its proved n² Gaussian
series, not assumed or inferred from a multivariable convention. -/
lemma affine_direction(x v:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j x≠0)
    (hk:fderiv ℂ (ratioVector τ hτ 1 j) x v=0):
    ∃c:ℂ,∃l:ComplexVectors→ₗ[ℂ]ℂ,∀a:ComplexVectors,
      fderiv ℂ F a v=(c+l a)*F a:=by
  have hs:=PELOriginalProjectiveRatioKernel318.scalar_ratios τ hτ x v j hj hk
  let k:=levelDirection τ hτ j x v/value τ hτ 3 j x
  have hc:∀r:Label 3,levelDirection τ hτ r x v=k*value τ hτ 3 r x:=
    common_slope τ hτ x v j hj hs
  have ht:=triple_directional τ hτ x v k hc
  let f:ComplexVectors→ℂ:=fun a=>F (x+a)
  let A:ComplexVectors→ℂ:=fun a=>direction τ hτ (x+a) v
  have hf:Differentiable ℂ f:=(PELOriginalGaugedTheta318.holomorphic τ hτ).comp
    (differentiable_const.add differentiable_id)
  have hA:Differentiable ℂ A:=(PELOriginalThetaDirectionalEntire318.directional_holomorphic τ hτ v).comp
    (differentiable_const.add differentiable_id)
  obtain ⟨p,hp⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  have hn:∃a,f a≠0:=by
    refine ⟨p-x,?_⟩
    change F (x+(p-x))≠0
    rw [show x+(p-x)=p by abel]
    exact hp
  obtain ⟨c,l,hl⟩:=EntireDifferentiatedTriple318.affine_variation f A hf hA hn k ht
  refine ⟨c-l x,l,?_⟩
  intro a
  have h:=hl (a-x)
  have he:x+(a-x)=a:=by abel
  simp only [f,A,direction,he,map_sub] at h
  convert h using 1 <;> ring

/-- Injectivity of the FULL complex Frechet derivative of every actual
level-three projective ratio chart, at every original covering point.
This is genuine tangent separation, separate from point injectivity. -/
theorem chart_derivative_injective(x:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j x≠0):
    Function.Injective (fderiv ℂ (ratioVector τ hτ 1 j) x):=by
  intro v w he
  have hz:fderiv ℂ (ratioVector τ hτ 1 j) x (v-w)=0:=by
    rw [map_sub,he,sub_self]
  obtain ⟨c,l,hl⟩:=affine_direction τ hτ x (v-w) j hj hz
  exact sub_eq_zero.mp (PELOriginalThetaInfinitesimalPeriod318.direction_zero τ hτ (v-w) c l hl)

/-- The derivative just proved injective is the derivative of the SAME
original map in genuine original source and independent target charts. -/
lemma original_chart_representation(x:ComplexVectors)(j:Label 3)(z:ComplexVectors):
    ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
      (projectiveMap τ hτ 1 ((DiscreteComplexPeriodAtlas318.localChart (P τ) x).symm z))=
        ratioVector τ hτ 1 j z:=by
  rw [DiscreteComplexPeriodAtlas318.localChart_symm,original_covering_square]
  exact actual_ratio τ hτ 1 j z

theorem original_chart_derivative_injective(x:ComplexVectors)(j:Label 3)
    (hj:value τ hτ 3 j x≠0):
    Function.Injective (fderiv ℂ (fun z:ComplexVectors=>
      ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
        (projectiveMap τ hτ 1 ((DiscreteComplexPeriodAtlas318.localChart (P τ) x).symm z))) x):=by
  have he:(fun z:ComplexVectors=>ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
      (projectiveMap τ hτ 1 ((DiscreteComplexPeriodAtlas318.localChart (P τ) x).symm z)))=
      ratioVector τ hτ 1 j:=funext (original_chart_representation τ hτ x j)
  rw [he]
  exact chart_derivative_injective τ hτ x j hj
end PELOriginalLevelThreeTangentSeparation318
