module
public import CenteredDifferentiatedTriple318
public import EntireBalancedTripleRigidity318
public section
noncomputable section
namespace EntireDifferentiatedTriple318
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
/-- Differentiated balanced triple rigidity for arbitrary entire F,
including zeros. The variation A is genuinely entire, not assumed to
be the product of F and an affine function. -/
theorem affine_variation(F A:E→ℂ)(hF:Differentiable ℂ F)(hA:Differentiable ℂ A)
    (hn:∃x,F x≠0)(k:ℂ)
    (ht:∀a b:E,A a*F b*F (-a-b)+F a*A b*F (-a-b)+F a*F b*A (-a-b)=
      k*(F a*F b*F (-a-b))):
    ∃c:ℂ,∃l:E→ₗ[ℂ]ℂ,∀x:E,A x=(c+l x)*F x:=by
  obtain ⟨a,ha,_,hb,_⟩:=EntireBalancedTripleRigidity318.common_center F F hF hF hn hn
  let f:E→ℂ:=fun x=>F (x+a)
  let g:E→ℂ:=fun x=>A (x+a)
  let H:E→ℂ:=fun x=>F (x-a-a)
  let B:E→ℂ:=fun x=>A (x-a-a)
  have hf:Differentiable ℂ f:=hF.comp (differentiable_id.add differentiable_const)
  have hg:Differentiable ℂ g:=hA.comp (differentiable_id.add differentiable_const)
  have hh:ContinuousAt H 0:=(hF.comp
    ((differentiable_id.sub differentiable_const).sub differentiable_const)).continuous.continuousAt
  obtain ⟨l,hl⟩:=CenteredDifferentiatedTriple318.affine_ratio f g H B k hf hg hh
    (by simpa only [f,zero_add] using ha)
    (by simpa only [H,zero_sub] using hb) (by
      intro x y
      have h:=ht (x+a) (y+a)
      have he:-(x+a)-(y+a)=(-x-y)-a-a:=by abel
      simpa only [f,g,H,B,he] using h)
  refine ⟨A a/F a-l a,l,?_⟩
  intro x
  have h:=hl (x-a)
  simp only [f,g,zero_add,sub_add_cancel,map_sub] at h
  convert h using 1 <;> ring
end EntireDifferentiatedTriple318
