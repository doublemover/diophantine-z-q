module
public import PELOriginalAutomorphyQuotient318
public import Mathlib.Topology.Constructions
public section
noncomputable section
namespace PELOriginalAutomorphyQuotientTopology318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPeriodLattice318
open PELOriginalAutomorphyRepresentatives318 PELOriginalAutomorphyQuotient318
open Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=original_discrete τ hτ

lemma shiftTo_locally_constant (a z:ComplexVectors)
    (ha:projection (P τ) z∈baseSet τ hτ a):
    ∀ᶠw in 𝓝 z,shiftTo τ hτ a w=shiftTo τ hτ a z:=by
  obtain ⟨d,_,hd⟩:=local_inverse_translation (P τ) a z ha
  have hz:=Filter.EventuallyEq.eq_of_nhds hd
  have hp:Continuous (projection (P τ)):=QuotientAddGroup.continuous_mk
  filter_upwards [hd,hp.continuousAt ((chart τ hτ a).open_source.mem_nhds ha)] with w hw hwa
  apply Subtype.ext
  rw [shiftTo_value τ hτ a w hwa,shiftTo_value τ hτ a z ha]
  change localChart (P τ) a (projection (P τ) w)-w=
    localChart (P τ) a (projection (P τ) z)-z
  rw [hw,hz]
  abel
lemma continuous_representative:Continuous (toTotal τ hτ):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) p.1)
  have ha:projection (P τ) p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hp:Continuous (fun x:ComplexVectors×ℂ=>projection (P τ) x.1):=
    QuotientAddGroup.continuous_mk.comp continuous_fst
  apply ((core τ hτ).localTriv a).continuousAt_of_comp_left hp.continuousAt ha
  have hc:ContinuousAt (fun x:ComplexVectors×ℂ=>
      (projection (P τ) x.1,factor τ hτ (shiftTo τ hτ a p.1) x.1*x.2)) p:=
    hp.continuousAt.prodMk
      (((holomorphic τ hτ _).continuous.comp continuous_fst).continuousAt.mul continuousAt_snd)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(shiftTo_locally_constant τ hτ a p.1 ha).comp_tendsto continuousAt_fst,
    hp.continuousAt ((chart τ hτ a).open_source.mem_nhds ha)] with x hx hxa
  change _=(core τ hτ).localTriv a (toTotal τ hτ x)
  rw [local_representative τ hτ a x hxa,hx]

/-- Actual local representative of a point of the produced bundle, using
its genuine local trivialization and the original quotient covering lift. -/
@[expose] def localRepresentative (a:ComplexVectors) (p:Total τ hτ):ComplexVectors×ℂ:=
  (chart τ hτ a p.1,((core τ hτ).localTriv a p).2)
lemma localRepresentative_continuousAt (a:ComplexVectors) (p:Total τ hτ)
    (hp:p.1∈baseSet τ hτ a):ContinuousAt (localRepresentative τ hτ a) p:=
  (((chart τ hτ a).continuousAt hp).comp p (projection_continuous τ hτ).continuousAt).prodMk
    (((core τ hτ).localTriv a).continuousAt hp).snd
lemma localRepresentative_rightInverse (a:ComplexVectors) (p:Total τ hτ)
    (hp:p.1∈baseSet τ hτ a):toTotal τ hτ (localRepresentative τ hτ a p)=p:=by
  let z:=chart τ hτ a p.1
  have hz:projection (P τ) z=p.1:=section_projection τ hτ a p.1 hp
  have hza:projection (P τ) z∈baseSet τ hτ a:=by rwa [hz]
  have hs:shiftTo τ hτ a z=0:=by
    apply Subtype.ext
    rw [shiftTo_value τ hτ a z hza,hz]
    exact sub_self _
  apply ((core τ hτ).localTriv a).injOn
  · change projection (P τ) z∈baseSet τ hτ a
    exact hza
  · exact hp
  rw [local_representative τ hτ a (localRepresentative τ hτ a p) hza]
  change (projection (P τ) z,factor τ hτ (shiftTo τ hτ a z) z*
    ((core τ hτ).localTriv a p).2)=(core τ hτ).localTriv a p
  rw [hz,hs,zero_factor,one_mul]
  exact Prod.ext (((core τ hτ).localTriv a).proj_toFun p hp).symm rfl

lemma inverse_locally_represented (a:ComplexVectors) (p:Total τ hτ)
    (hp:p.1∈baseSet τ hτ a):
    (equivalence τ hτ).symm p=Quotient.mk _ (localRepresentative τ hτ a p):=by
  apply (equivalence τ hτ).injective
  rw [Equiv.apply_symm_apply,actual_representative,localRepresentative_rightInverse τ hτ a p hp]
lemma inverse_continuous:Continuous (equivalence τ hτ).symm:=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  have hp:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hc:ContinuousAt (fun r:Total τ hτ=>
      (Quotient.mk (orbitSetoid τ hτ) (localRepresentative τ hτ a r))) p:=
    continuous_quotient_mk'.continuousAt.comp p (localRepresentative_continuousAt τ hτ a p hp)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(projection_continuous τ hτ).continuousAt
    ((chart τ hτ a).open_source.mem_nhds hp)] with r hr
  exact (inverse_locally_represented τ hτ a r hr).symm

/-- HOMEOMORPHISM with the actual action-quotient topology on one side
and the independently constructed bundle-core topology on the other.
Both directions are continuous from actual local representatives. -/
@[expose] def homeomorph:Orbit τ hτ≃ₜTotal τ hτ where
  toEquiv:=equivalence τ hτ
  continuous_toFun:=(continuous_representative τ hτ).quotient_lift _
  continuous_invFun:=inverse_continuous τ hτ
lemma homeomorph_representative (p:ComplexVectors×ℂ):
    homeomorph τ hτ (Quotient.mk _ p)=toTotal τ hτ p:=rfl
end PELOriginalAutomorphyQuotientTopology318
