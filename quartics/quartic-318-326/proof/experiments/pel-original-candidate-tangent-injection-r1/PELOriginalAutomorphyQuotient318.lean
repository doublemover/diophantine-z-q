module
public import PELOriginalAutomorphyRepresentatives318
public section
noncomputable section
namespace PELOriginalAutomorphyQuotient318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPeriodLattice318
open PELOriginalAutomorphyRepresentatives318 PELOriginalDescendedMetric318
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=original_discrete τ hτ

/-- Literal orbit relation of the constructed original lattice action. -/
@[expose] def orbitSetoid:Setoid (ComplexVectors×ℂ) where
  r p q:=∃l:L τ hτ,action τ hτ l p=q
  iseqv:=⟨fun p=>⟨0,action_zero τ hτ p⟩,
    by
      rintro p q ⟨l,rfl⟩
      refine ⟨-l,?_⟩
      rw [←action_add,neg_add_cancel,action_zero],
    by
      rintro p q r ⟨l,rfl⟩ ⟨m,rfl⟩
      exact ⟨m+l,action_add τ hτ m l p⟩⟩
lemma same_cover_fiber (z:ComplexVectors) (v w:ℂ)
    (h:toTotal τ hτ (z,v)=toTotal τ hτ (z,w)):v=w:=by
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) z)
  have ha:projection (P τ) z∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have he:=congrArg (fun r:Total τ hτ=>((core τ hτ).localTriv a r).2) h
  rw [local_representative τ hτ a (z,v) ha,local_representative τ hτ a (z,w) ha] at he
  exact mul_left_cancel₀ (nonzero τ hτ (shiftTo τ hτ a z) z) he
lemma representative_surjective:Function.Surjective (toTotal τ hτ):=by
  rintro ⟨q,v⟩
  let a:ComplexVectors:=(core τ hτ).indexAt q
  let z:=chart τ hτ a q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hz:projection (P τ) z=q:=section_projection τ hτ a q ha
  have hs:shiftTo τ hτ a z=0:=by
    apply Subtype.ext
    have hza:projection (P τ) z∈baseSet τ hτ a:=by rwa [hz]
    rw [shiftTo_value τ hτ a z hza,hz]
    exact sub_self _
  refine ⟨(z,v),?_⟩
  simp only [toTotal,hz]
  change (⟨q,factor τ hτ (shiftTo τ hτ a z) z*v⟩:Total τ hτ)=⟨q,v⟩
  rw [hs,zero_factor,one_mul]

/-- Exact full fibers, including the zero section, are ORIGINAL action
orbits. The fiber multiplier is nonzero because it is the actual exponential. -/
theorem exact_orbits (p q:ComplexVectors×ℂ):
    toTotal τ hτ p=toTotal τ hτ q↔(orbitSetoid τ hτ).r p q:=by
  constructor
  · intro he
    have hp:projection (P τ) p.1=projection (P τ) q.1:=congrArg
      (fun r:Total τ hτ=>r.1) he
    have hm:q.1-p.1∈lattice τ hτ:=by
      rw [←exact_period_subgroup τ hτ]
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' (P τ)) (_-_)=0
      rw [map_sub]
      change projection (P τ) q.1-projection (P τ) p.1=0
      rw [hp,sub_self]
    let l:L τ hτ:=⟨q.1-p.1,hm⟩
    have hx:(action τ hτ l p).1=q.1:=by change p.1+(q.1-p.1)=q.1;abel
    have hpair:action τ hτ l p=(q.1,(action τ hτ l p).2):=Prod.ext hx rfl
    have hy:(action τ hτ l p).2=q.2:=by
      apply same_cover_fiber τ hτ q.1
      rw [←hpair,toTotal_action]
      exact he
    exact ⟨l,Prod.ext hx hy⟩
  · rintro ⟨l,rfl⟩
    exact (toTotal_action τ hτ l p).symm

abbrev Orbit:=Quotient (orbitSetoid τ hτ)
@[expose] def quotientMap:Orbit τ hτ→Total τ hτ:=
  Quotient.lift (toTotal τ hτ) (fun p q h=>(exact_orbits τ hτ p q).mpr h)
@[expose] def equivalence:Orbit τ hτ≃Total τ hτ:=Equiv.ofBijective (quotientMap τ hτ) (by
  constructor
  · intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro x y h
    exact Quotient.sound ((exact_orbits τ hτ x y).mp h)
  · intro p
    obtain ⟨x,hx⟩:=representative_surjective τ hτ p
    exact ⟨Quotient.mk _ x,hx⟩)
lemma actual_representative (p:ComplexVectors×ℂ):
    equivalence τ hτ (Quotient.mk _ p)=toTotal τ hτ p:=rfl

/-- The actual orbit quotient metric is well-defined from the original
Gaussian norm and agrees with the independently constructed bundle metric. -/
@[expose] def orbitMetric:Orbit τ hτ→ℝ:=Quotient.lift
  (PELOriginalPolarizationMetric318.squaredNorm τ hτ) (by
    rintro p q ⟨l,rfl⟩
    exact (PELOriginalPolarizationMetric318.squaredNorm_action τ hτ l p).symm)
lemma metric_comparison (p:Orbit τ hτ):
    metric τ hτ (equivalence τ hτ p)=orbitMetric τ hτ p:=by
  induction p using Quotient.inductionOn with
  | h x=>exact metric_representative τ hτ x
end PELOriginalAutomorphyQuotient318
