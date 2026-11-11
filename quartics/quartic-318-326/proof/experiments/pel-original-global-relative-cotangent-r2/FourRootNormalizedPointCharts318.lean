module
public import FourRootInfinityExtension318
public section
noncomputable section
namespace FourRootNormalizedPointCharts318
open Set
open scoped OnePoint
variable (b:Fin 4→ℂ)

/-- Genuine finite affine equations, with their inherited complex-plane
subspace topology; the branch constants are NOT specialized prematurely. -/
abbrev FinitePoints:={p:ℂ×(Fin 4→ℂ)//∀k,(p.2 k)^2=p.1-b k}
/-- Normalized infinity chart: u=1/z0 and s_k=z_k/z0. Keeping all three
sign ratios separates the eight points above infinity. -/
abbrev InfinityPoints:={p:ℂ×(Fin 4→ℂ)//p.2 0=1 ∧
  ∀k,(p.2 k)^2=1+(b 0-b k)*p.1^2}
abbrev InfinitySigns:={s:Fin 4→ℂ//s 0=1 ∧ ∀k,(s k)^2=1}
abbrev FiniteOverlap:={p:FinitePoints b//p.val.2 0≠0}
abbrev InfinityOverlap:={p:InfinityPoints b//p.val.1≠0}

/-- Exact finite-to-infinity overlap, with NO root choices. -/
@[expose] def toInfinity (p:FiniteOverlap b) : InfinityOverlap b:=by
  let u:ℂ:=(p.val.val.2 0)⁻¹
  let s:Fin 4→ℂ:=fun k=>p.val.val.2 k/p.val.val.2 0
  refine ⟨⟨(u,s),?_,?_⟩,inv_ne_zero p.property⟩
  · exact div_self p.property
  · intro k
    dsimp [s,u]
    rw [div_pow,inv_pow]
    field_simp [p.property]
    rw [p.val.property k,p.val.property 0]
    ring

/-- Exact inverse, preserving the original affine base t=b0+u^-2. -/
@[expose] def toFinite (p:InfinityOverlap b) : FiniteOverlap b:=by
  let t:ℂ:=b 0+(p.val.val.1^2)⁻¹
  let z:Fin 4→ℂ:=fun k=>p.val.val.2 k/p.val.val.1
  refine ⟨⟨(t,z),?_⟩,?_⟩
  · intro k
    dsimp [z,t]
    rw [div_pow,p.val.property.2 k]
    field_simp [p.property]
    ring
  · change p.val.val.2 0/p.val.val.1≠0
    rw [p.val.property.1]
    exact div_ne_zero one_ne_zero p.property

lemma toFinite_toInfinity (p:FiniteOverlap b) : toFinite b (toInfinity b p)=p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change b 0+((p.val.val.2 0)⁻¹^2)⁻¹=p.val.val.1
    rw [inv_pow,inv_inv,p.val.property 0]
    ring
  · funext k
    change (p.val.val.2 k/p.val.val.2 0)/(p.val.val.2 0)⁻¹=p.val.val.2 k
    field_simp [p.property]

lemma toInfinity_toFinite (p:InfinityOverlap b) : toInfinity b (toFinite b p)=p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (p.val.val.2 0/p.val.val.1)⁻¹=p.val.val.1
    rw [p.val.property.1,one_div,inv_inv]
  · funext k
    change (p.val.val.2 k/p.val.val.1)/(p.val.val.2 0/p.val.val.1)=p.val.val.2 k
    rw [p.val.property.1]
    field_simp [p.property]

@[expose] def overlapEquiv : FiniteOverlap b≃InfinityOverlap b where
  toFun:=toInfinity b
  invFun:=toFinite b
  left_inv:=toFinite_toInfinity b
  right_inv:=toInfinity_toFinite b

/-- Only the actual missing points are appended. Infinity is eight
separate sign triples, never one point per singular character tuple. -/
abbrev Completed:=FinitePoints b⊕InfinitySigns
@[expose] def finiteChart (p:FinitePoints b):Completed b:=Sum.inl p
@[expose] def infinityChart (p:InfinityPoints b):Completed b:=
  if h:p.val.1=0 then .inr ⟨p.val.2,p.property.1,by
    intro k
    simpa only [h,zero_pow (by decide:2≠0),mul_zero,add_zero] using p.property.2 k⟩
  else .inl (toFinite b ⟨p,h⟩).val

lemma infinityChart_nonzero (p:InfinityPoints b) (h:p.val.1≠0) :
    infinityChart b p=.inl (toFinite b ⟨p,h⟩).val:=dif_neg h
lemma infinityChart_zero (s:InfinitySigns) :
    infinityChart b ⟨(0,s.val),s.property.1,by
      intro k
      simpa only [zero_pow (by decide:2≠0),mul_zero,add_zero] using s.property.2 k⟩=.inr s:=by
  simp only [infinityChart,dif_pos rfl]

lemma infinityChart_injective : Function.Injective (infinityChart b) := by
  intro p q h
  by_cases hp:p.val.1=0 <;> by_cases hq:q.val.1=0
  · rw [infinityChart,dif_pos hp,infinityChart,dif_pos hq] at h
    apply Subtype.ext
    apply Prod.ext
    · exact hp.trans hq.symm
    · exact congrArg Subtype.val (Sum.inr.inj h)
  · rw [infinityChart,dif_pos hp,infinityChart,dif_neg hq] at h
    cases h
  · rw [infinityChart,dif_neg hp,infinityChart,dif_pos hq] at h
    cases h
  · rw [infinityChart,dif_neg hp,infinityChart,dif_neg hq] at h
    have hh:toFinite b ⟨p,hp⟩=toFinite b ⟨q,hq⟩:=Subtype.ext (Sum.inl.inj h)
    exact congrArg Subtype.val ((overlapEquiv b).symm.injective hh)

lemma overlap_agreement (p:FiniteOverlap b) :
    infinityChart b (toInfinity b p).val=finiteChart b p.val:=by
  rw [infinityChart_nonzero _ _ (toInfinity b p).property]
  exact congrArg (fun x:FiniteOverlap b=>Sum.inl x.val) (toFinite_toInfinity b p)

/-- Both true affine charts jointly cover the entire normalized point
carrier. No geometry is deduced merely from this set-theoretic cover. -/
theorem charts_cover (p:Completed b) :
    (∃q:FinitePoints b,finiteChart b q=p) ∨ (∃q:InfinityPoints b,infinityChart b q=p) := by
  rcases p with p|s
  · exact Or.inl ⟨p,rfl⟩
  · refine Or.inr ⟨⟨(0,s.val),s.property.1,?_⟩,infinityChart_zero b s⟩
    intro k
    simpa only [zero_pow (by decide:2≠0),mul_zero,add_zero] using s.property.2 k

@[expose] def projection : Completed b→OnePoint ℂ
  | .inl p=>(p.val.1:OnePoint ℂ)
  | .inr _=>∞
lemma infinity_projection_nonzero (p:InfinityPoints b) (h:p.val.1≠0) :
    projection b (infinityChart b p)=((b 0+(p.val.1^2)⁻¹):ℂ):=by
  rw [infinityChart_nonzero b p h]
  rfl
end FourRootNormalizedPointCharts318
