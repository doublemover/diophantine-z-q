module
public import ComplexTorusCoverLift318
public import Mathlib.GroupTheory.Index
public section
noncomputable section
namespace ComplexTorusCoverPeriods318
open Set Topology
open ComplexLineLatticeAtlas318 ComplexTorusCoverLift318
variable (L:AddSubgroup ℂ) [DiscreteTopology L]
variable {E:Type*} [TopologicalSpace E]
variable (p:E→Quotient L) (cov:IsCoveringMap p) (e₀:E) (he:p e₀=projection L 0)

/-- The ACTUAL global periods of the constructed lift, not a chosen
finite-index subgroup or a group transported from an abstract torus. -/
@[expose] def periods : AddSubgroup ℂ where
  carrier:={a|∀z,lift L p cov e₀ he (z+a)=lift L p cov e₀ he z}
  zero_mem':=by intro z;rw [add_zero]
  add_mem':=by
    intro a b ha hb z
    rw [←add_assoc,hb,ha]
  neg_mem':=by
    intro a ha z
    have hh:=ha (z-a)
    simpa only [sub_add_cancel,sub_eq_add_neg] using hh.symm
lemma period_iff (a:ℂ) : a∈periods L p cov e₀ he ↔
    ∀z,lift L p cov e₀ he (z+a)=lift L p cov e₀ he z :=Iff.rfl

/-- Every true source period belongs to the SAME target lattice, directly
from the commuting original covering square. -/
lemma periods_le : periods L p cov e₀ he≤L := by
  intro a ha
  have hh:=congrArg p (ha 0)
  simp only [zero_add,lift_projection] at hh
  apply (QuotientAddGroup.eq_zero_iff).mp
  simpa only [projection,map_zero] using hh

/-- Equality at ONE point propagates to a true global period by uniqueness
of lifts through the ORIGINAL cover. No affine or translation action on
the original source is assumed. -/
lemma period_of_equal_at (a z:ℂ) (ha:a∈L)
    (hz:lift L p cov e₀ he (z+a)=lift L p cov e₀ he z) :
    a∈periods L p cov e₀ he := by
  have hbase:p ∘ (fun w=>lift L p cov e₀ he (w+a))=p ∘ lift L p cov e₀ he:=by
    funext w
    simp only [Function.comp_apply,lift_projection]
    change (QuotientAddGroup.mk' L)(w+a)=(QuotientAddGroup.mk' L)w
    rw [map_add,show (QuotientAddGroup.mk' L)a=0 from (QuotientAddGroup.eq_zero_iff).mpr ha,add_zero]
  have hh:=cov.eq_of_comp_eq
    ((lift L p cov e₀ he).continuous.comp (continuous_id.add continuous_const))
    (lift L p cov e₀ he).continuous hbase z hz
  exact fun w=>congrFun hh w

/-- The complete fiber relation of the actual complex-line lift. This is
what permits a quotient homeomorphism, rather than guessing periods from
one local chart or merely matching fiber cardinalities. -/
theorem fiber_iff (z w:ℂ) : lift L p cov e₀ he z=lift L p cov e₀ he w ↔
    z-w∈periods L p cov e₀ he := by
  constructor
  · intro h
    have hp:=congrArg p h
    rw [lift_projection,lift_projection] at hp
    have ha:z-w∈L:=by
      apply (QuotientAddGroup.eq_zero_iff).mp
      change (QuotientAddGroup.mk' L)(z-w)=0
      rw [map_sub,hp,sub_self]
    apply period_of_equal_at L p cov e₀ he (z-w) w ha
    have hsum:w+(z-w)=z:=by ring
    simpa only [hsum] using h
  · intro h
    have hh:=h w
    have hsum:w+(z-w)=z:=by ring
    simpa only [hsum] using hh
lemma period_iff_center (a:ℂ) : a∈periods L p cov e₀ he ↔ lift L p cov e₀ he a=e₀ := by
  constructor
  · intro ha
    have hh:=ha 0
    simpa only [zero_add,lift_zero] using hh
  · intro ha
    have hh:lift L p cov e₀ he a=lift L p cov e₀ he 0:=
      ha.trans (lift_zero L p cov e₀ he).symm
    simpa only [sub_zero] using (fiber_iff L p cov e₀ he a 0).mp hh

/-- The lift's period subgroup is discrete in the ORIGINAL complex-line
topology, since it is a subgroup of the already discrete actual lattice. -/
instance periods_discrete : DiscreteTopology (periods L p cov e₀ he) := by
  apply isDiscrete_iff_discreteTopology.mp
  exact (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology L)).mono
    (periods_le L p cov e₀ he)
end ComplexTorusCoverPeriods318
