module
public import PELOriginalPowerSectionLift318
public section
noncomputable section
namespace PELOriginalPowerSectionDescent318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalPolarizationAutomorphy318
open PELOriginalAutomorphyRepresentatives318 PELOriginalPowerSectionLift318
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- Full original-factor automorphic functions, before any theta gauge
or normalized period coordinates are introduced. -/
structure OriginalAutomorphic where
  value:ComplexVectors→ℂ
  entire:Differentiable ℂ value
  lattice_rule:∀l:L τ hτ,∀z,value (z+l.val)=factor τ hτ l z^N*value z
@[expose] def descend(f:OriginalAutomorphic τ hτ N):HolomorphicSection τ hτ N where
  value q:=(powerSection τ hτ N f.value q).2
  holomorphic a:=holomorphic_section τ hτ N f.value f.entire f.lattice_rule a
@[expose] def ascend(s:HolomorphicSection τ hτ N):OriginalAutomorphic τ hτ N where
  value:=lift τ hτ N s
  entire:=PELOriginalPowerSectionLift318.entire τ hτ N s
  lattice_rule:=PELOriginalPowerSectionLift318.original_automorphy τ hτ N s

lemma lift_descend(f:OriginalAutomorphic τ hτ N)(z:ComplexVectors):
    lift τ hτ N (descend τ hτ N f) z=f.value z:=by
  let q:=projection (P τ) z
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  have hs:z+(shiftTo τ hτ a z:ComplexVectors)=chart τ hτ a q:=by
    rw [shiftTo_value τ hτ a z ha];abel
  have hf:=f.lattice_rule (shiftTo τ hτ a z) z
  rw [hs] at hf
  change (factor τ hτ (shiftTo τ hτ a z) z^N)⁻¹*f.value (chart τ hτ a q)=f.value z
  rw [hf]
  exact inv_mul_cancel_left₀ (pow_ne_zero N (nonzero τ hτ _ _)) _

lemma descend_lift(s:HolomorphicSection τ hτ N)(q:Base τ):
    (descend τ hτ N (ascend τ hτ N s)).value q=s.value q:=by
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  let z:=chart τ hτ a q
  have hz:z∈(chart τ hτ a).target:=(chart τ hτ a).map_source ha
  have hp:projection (P τ) z=q:=section_projection τ hτ a q ha
  have hs:shiftTo τ hτ a z=0:=target_shift_zero τ hτ a z hz
  change (factor τ hτ (shiftTo τ hτ ((core τ hτ).indexAt (projection (P τ) z)) z) z^N)⁻¹*
    s.value (projection (P τ) z)=s.value q
  simp only [hp,hs,zero_factor,one_pow,inv_one,one_mul]

/-- Genuine whole-section correspondence: BOTH directions are derived
from original local bundle coordinates. In particular arbitrary sections
are not defined to be functions already in the theta span. -/
@[expose] def equivalence:HolomorphicSection τ hτ N≃OriginalAutomorphic τ hτ N where
  toFun:=ascend τ hτ N
  invFun:=descend τ hτ N
  left_inv s:=by
    cases s with
    | mk v hv =>
      have he:(descend τ hτ N (ascend τ hτ N ⟨v,hv⟩)).value=v:=by
        funext q;exact descend_lift τ hτ N ⟨v,hv⟩ q
      cases he
      rfl
  right_inv f:=by
    cases f with
    | mk v hv ha =>
      have he:(ascend τ hτ N (descend τ hτ N ⟨v,hv,ha⟩)).value=v:=by
        funext z;exact lift_descend τ hτ N ⟨v,hv,ha⟩ z
      cases he
      rfl

/-- Continuity of an arbitrary original holomorphic section is DERIVED
from its recovered entire representative and genuine original gluing. -/
theorem continuous_total(s:HolomorphicSection τ hτ N):Continuous (total τ hτ N s):=by
  have h:=continuous_section τ hτ N (lift τ hτ N s)
    (PELOriginalPowerSectionLift318.entire τ hτ N s).continuous
    (PELOriginalPowerSectionLift318.original_automorphy τ hτ N s)
  have he:powerSection τ hτ N (lift τ hτ N s)=total τ hτ N s:=by
    funext q
    exact congrArg (fun v:PowerFiber τ hτ N q=>(⟨q,v⟩:PowerTotal τ hτ N))
      (descend_lift τ hτ N s q)
  rwa [he] at h
end PELOriginalPowerSectionDescent318
