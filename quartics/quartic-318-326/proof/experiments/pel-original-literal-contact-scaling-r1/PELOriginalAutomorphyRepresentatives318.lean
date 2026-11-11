module
public import PELOriginalDescendedMetric318
public section
noncomputable section
namespace PELOriginalAutomorphyRepresentatives318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPeriodLattice318
open PELOriginalDescendedMetric318
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=original_discrete τ hτ

lemma projection_add_period (z:ComplexVectors) (l:L τ hτ):
    projection (P τ) (z+l.val)=projection (P τ) z:=by
  have hl:l.val∈P τ:=by rw [exact_period_subgroup τ hτ];exact l.property
  change (QuotientAddGroup.mk' (P τ)) (z+l.val)=(QuotientAddGroup.mk' (P τ)) z
  rw [map_add,(QuotientAddGroup.eq_zero_iff _).mpr hl,add_zero]
lemma section_difference (a z:ComplexVectors)
    (ha:projection (P τ) z∈baseSet τ hτ a):
    chart τ hτ a (projection (P τ) z)-z∈lattice τ hτ:=by
  rw [←exact_period_subgroup τ hτ]
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' (P τ)) (_-_)=0
  rw [map_sub]
  change projection (P τ) (chart τ hτ a (projection (P τ) z))-projection (P τ) z=0
  rw [section_projection τ hτ a _ ha,sub_self]
@[expose] def shiftTo (a z:ComplexVectors):L τ hτ:=
  if h:projection (P τ) z∈baseSet τ hτ a then
    ⟨chart τ hτ a (projection (P τ) z)-z,section_difference τ hτ a z h⟩ else 0
lemma shiftTo_value (a z:ComplexVectors) (ha:projection (P τ) z∈baseSet τ hτ a):
    (shiftTo τ hτ a z:ComplexVectors)=chart τ hτ a (projection (P τ) z)-z:=by
  simp [shiftTo,ha]
lemma shiftTo_change (a b z:ComplexVectors)
    (ha:projection (P τ) z∈baseSet τ hτ a)
    (hb:projection (P τ) z∈baseSet τ hτ b):
    shift τ hτ a b (projection (P τ) z)+shiftTo τ hτ a z=shiftTo τ hτ b z:=by
  apply Subtype.ext
  simp only [Submodule.coe_add,shift_value τ hτ a b _ ha hb,
    shiftTo_value τ hτ a z ha,shiftTo_value τ hτ b z hb]
  abel
lemma factor_change (a b z:ComplexVectors)
    (ha:projection (P τ) z∈baseSet τ hτ a)
    (hb:projection (P τ) z∈baseSet τ hτ b):
    factor τ hτ (shiftTo τ hτ b z) z=
      transition τ hτ a b (projection (P τ) z)*factor τ hτ (shiftTo τ hτ a z) z:=by
  rw [←shiftTo_change τ hτ a b z ha hb,cocycle]
  have h:z+(shiftTo τ hτ a z:ComplexVectors)=chart τ hτ a (projection (P τ) z):=by
    rw [shiftTo_value τ hτ a z ha];abel
  rw [h]
  rfl

/-- The actual representative map from the original trivial line C²×C
into the SAME produced line bundle. It uses the original factor, not a
new fiber equivalence with unrelated automorphy. -/
@[expose] def toTotal (p:ComplexVectors×ℂ):Total τ hτ:=
  let q:=projection (P τ) p.1
  ⟨q,factor τ hτ (shiftTo τ hτ ((core τ hτ).indexAt q) p.1) p.1*p.2⟩
lemma local_representative (a:ComplexVectors) (p:ComplexVectors×ℂ)
    (ha:projection (P τ) p.1∈baseSet τ hτ a):
    (core τ hτ).localTriv a (toTotal τ hτ p)=
      (projection (P τ) p.1,factor τ hτ (shiftTo τ hτ a p.1) p.1*p.2):=by
  apply Prod.ext
  · rfl
  · change transition τ hτ ((core τ hτ).indexAt (projection (P τ) p.1)) a
      (projection (P τ) p.1)*(factor τ hτ
        (shiftTo τ hτ ((core τ hτ).indexAt (projection (P τ) p.1)) p.1) p.1*p.2)=_
    rw [←mul_assoc,←factor_change τ hτ _ a p.1 ((core τ hτ).mem_baseSet_at _) ha]

lemma metric_representative (p:ComplexVectors×ℂ):
    metric τ hτ (toTotal τ hτ p)=PELOriginalPolarizationMetric318.squaredNorm τ hτ p:=by
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) p.1)
  have ha:projection (P τ) p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have h:p.1+(shiftTo τ hτ a p.1:ComplexVectors)=chart τ hτ a (projection (P τ) p.1):=by
    rw [shiftTo_value τ hτ a p.1 ha];abel
  have he:=PELOriginalPolarizationMetric318.squaredNorm_action τ hτ (shiftTo τ hτ a p.1) p
  simpa only [action,h] using he

lemma shiftTo_period (a z:ComplexVectors) (l:L τ hτ)
    (ha:projection (P τ) z∈baseSet τ hτ a):
    shiftTo τ hτ a (z+l.val)+l=shiftTo τ hτ a z:=by
  have hb:projection (P τ) (z+l.val)∈baseSet τ hτ a:=by
    rwa [projection_add_period]
  apply Subtype.ext
  simp only [Submodule.coe_add,shiftTo_value τ hτ a _ hb,
    shiftTo_value τ hτ a z ha,projection_add_period]
  abel
lemma toTotal_action (l:L τ hτ) (p:ComplexVectors×ℂ):
    toTotal τ hτ (action τ hτ l p)=toTotal τ hτ p:=by
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) p.1)
  have ha:projection (P τ) p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hc:=cocycle τ hτ (shiftTo τ hτ a (p.1+l.val)) l p.1
  rw [shiftTo_period τ hτ a p.1 l ha] at hc
  simp only [toTotal,action,projection_add_period]
  congr 1
  change factor τ hτ (shiftTo τ hτ a (p.1+l.val)) (p.1+l.val)*
    (factor τ hτ l p.1*p.2)=factor τ hτ (shiftTo τ hτ a p.1) p.1*p.2
  rw [←mul_assoc,←hc]
end PELOriginalAutomorphyRepresentatives318
