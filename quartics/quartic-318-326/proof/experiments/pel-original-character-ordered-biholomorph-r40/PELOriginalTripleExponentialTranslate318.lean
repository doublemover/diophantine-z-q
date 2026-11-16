module
public import PELOriginalTripleEvaluation318
public section
noncomputable section
namespace PELOriginalTripleExponentialTranslate318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
variable (τ:ℂ)(hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- Actual level-three projective equality produces the precise entire
exponential translate symmetry consumed by the independent original
lattice-character theorem. No global zero-free theta or logarithm is used. -/
theorem produced_translate(x y:ComplexVectors)
    (h:projectiveMap τ hτ 1 (projection (P τ) x)=
      projectiveMap τ hτ 1 (projection (P τ) y)):
    ∃C:ℂ,C≠0∧∃l:ComplexVectors→ₗ[ℂ]ℂ,
      ∀a:ComplexVectors,F (a+(x-y))=C*Complex.exp (l a)*F a:=by
  obtain ⟨C,hC,ht⟩:=PELOriginalTripleEvaluation318.triple_proportional τ hτ x y h
  obtain ⟨p,hp⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  let f:ComplexVectors→ℂ:=fun a=>F (x+a)
  let g:ComplexVectors→ℂ:=fun a=>F (y+a)
  have hf:Differentiable ℂ f:=(PELOriginalGaugedTheta318.holomorphic τ hτ).comp
    (differentiable_const.add differentiable_id)
  have hg:Differentiable ℂ g:=(PELOriginalGaugedTheta318.holomorphic τ hτ).comp
    (differentiable_const.add differentiable_id)
  have hfn:∃a,f a≠0:=by
    refine ⟨p-x,?_⟩
    change F (x+(p-x))≠0
    rw [show x+(p-x)=p by abel]
    exact hp
  have hgn:∃a,g a≠0:=by
    refine ⟨p-y,?_⟩
    change F (y+(p-y))≠0
    rw [show y+(p-y)=p by abel]
    exact hp
  obtain ⟨D,hD,l,hl⟩:=EntireBalancedTripleRigidity318.exponential_ratio f g hf hg hfn hgn C ht
  refine ⟨D*Complex.exp (-l y),mul_ne_zero hD (Complex.exp_ne_zero _),l,?_⟩
  intro a
  have he:=hl (a-y)
  have hx:x+(a-y)=a+(x-y):=by abel
  have hy:y+(a-y)=a:=by abel
  simp only [f,g,hx,hy,map_sub,sub_eq_add_neg,Complex.exp_add] at he
  rw [he]
  ring
end PELOriginalTripleExponentialTranslate318
