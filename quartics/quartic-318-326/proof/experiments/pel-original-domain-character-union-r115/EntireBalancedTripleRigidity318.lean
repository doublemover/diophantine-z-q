module
public import CenteredTripleProductRigidity318
public section
noncomputable section
namespace EntireBalancedTripleRigidity318
open Set Filter Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]

/-- A common center and its required compensating third point are
produced outside all four actual zero loci. This is finite avoidance
for genuine entire functions, not an assumed zero-free theta. -/
lemma common_center(F G:E→ℂ)(hF:Differentiable ℂ F)(hG:Differentiable ℂ G)
    (hnF:∃a,F a≠0)(hnG:∃a,G a≠0):
    ∃a,F a≠0∧G a≠0∧F (-a-a)≠0∧G (-a-a)≠0:=by
  let P:E→ℂ:=fun a=>F a*G a
  have hP:Differentiable ℂ P:=hF.mul hG
  obtain ⟨p,hp⟩:=EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero F G hF hG hnF hnG
  let c:ℂ:=-2
  have hc:c≠0:=by norm_num [c]
  have hPc:Differentiable ℂ (fun a:E=>P (c • a)):=hP.comp (differentiable_id.const_smul c)
  have hnc:∃a:E,P (c • a)≠0:=by
    refine ⟨c⁻¹ • p,?_⟩
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
    exact hp
  obtain ⟨a,ha⟩:=EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero
    P (fun a=>P (c • a)) hP hPc ⟨p,hp⟩ hnc
  have h:=mul_ne_zero_iff.mp ha
  have he:c • a=-a-a:=by simp only [c,neg_smul,two_smul,neg_add,sub_eq_add_neg]
  rw [he] at h
  exact ⟨a,(mul_ne_zero_iff.mp h.1).1,(mul_ne_zero_iff.mp h.1).2,
    (mul_ne_zero_iff.mp h.2).1,(mul_ne_zero_iff.mp h.2).2⟩

/-- Balanced triple evaluation proportionality forces a NONZERO entire
exponential translate ratio, through all zeros of both factors. The only
ratios used in the proof live near an internally produced common center. -/
theorem exponential_ratio(F G:E→ℂ)(hF:Differentiable ℂ F)(hG:Differentiable ℂ G)
    (hnF:∃a,F a≠0)(hnG:∃a,G a≠0)(C:ℂ)
    (ht:∀a b:E,F a*F b*F (-a-b)=C*(G a*G b*G (-a-b))):
    ∃D:ℂ,D≠0∧∃l:E→ₗ[ℂ]ℂ,∀a:E,F a=D*Complex.exp (l a)*G a:=by
  obtain ⟨a,haF,haG,haH,haK⟩:=common_center F G hF hG hnF hnG
  let F':E→ℂ:=fun x=>F (x+a)
  let G':E→ℂ:=fun x=>G (x+a)
  let H:E→ℂ:=fun x=>F (x-a-a)
  let K:E→ℂ:=fun x=>G (x-a-a)
  have hd:Differentiable ℂ (fun x:E=>x+a):=differentiable_id.add_const a
  have hH:ContinuousAt H 0:=
    (hF.comp ((differentiable_id.sub_const a).sub_const a)).continuous.continuousAt
  have htr:∀x y:E,F' x*F' y*H (-x-y)=C*(G' x*G' y*K (-x-y)):=by
    intro x y
    have he:-(x+a)-(y+a)=(-x-y)-a-a:=by abel
    simpa only [F',G',H,K,he] using ht (x+a) (y+a)
  obtain ⟨l,hl⟩:=CenteredTripleProductRigidity318.exponential_ratio F' G' H K C
    (hF.comp hd) (hG.comp hd) hH
    (by simpa only [F',zero_add] using haF)
    (by simpa only [G',zero_add] using haG)
    (by simpa only [H,zero_sub] using haH) htr
  let D:ℂ:=(F a/G a)*Complex.exp (-l a)
  have hD:D≠0:=mul_ne_zero (div_ne_zero haF haG) (Complex.exp_ne_zero _)
  refine ⟨D,hD,l,?_⟩
  intro x
  have h:=hl (x-a)
  simp only [F',G',sub_add_cancel,zero_add,map_sub] at h
  rw [h]
  simp only [D,sub_eq_add_neg,Complex.exp_add]
  ring
end EntireBalancedTripleRigidity318
