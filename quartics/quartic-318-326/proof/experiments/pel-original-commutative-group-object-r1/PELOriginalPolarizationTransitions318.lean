module
public import PELOriginalPolarizationMetric318
public import PELComplexPeriodSurface318
public import Mathlib.Topology.VectorBundle.Basic
public section
noncomputable section
namespace PELOriginalPolarizationTransitions318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPeriodLattice318
open Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)
abbrev P:=PELComplexPeriodSurface318.Periods τ
abbrev Base:=PELComplexPeriodSurface318.Surface τ
local instance discretePeriods:DiscreteTopology (P τ):=original_discrete τ hτ
local instance discreteLattice:DiscreteTopology (L τ hτ):=by
  have h:=original_discrete τ hτ
  rw [exact_period_subgroup τ hτ] at h
  exact h
@[expose] def chart (a:ComplexVectors):OpenPartialHomeomorph (Base τ) ComplexVectors:=
  localChart (P τ) a
@[expose] def baseSet (a:ComplexVectors):Set (Base τ):=(chart τ hτ a).source
lemma section_projection (a:ComplexVectors) (q:Base τ) (hq:q∈baseSet τ hτ a):
    projection (P τ) (chart τ hτ a q)=q:=by
  have h:=(chart τ hτ a).left_inv hq
  simpa only [chart,localChart_symm] using h
lemma difference_mem (a b:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b):
    chart τ hτ b q-chart τ hτ a q∈lattice τ hτ:=by
  rw [←exact_period_subgroup τ hτ]
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' (P τ)) (_-_)=0
  rw [map_sub]
  change projection (P τ) (chart τ hτ b q)-projection (P τ) (chart τ hτ a q)=0
  rw [section_projection τ hτ b q hb,section_projection τ hτ a q ha,sub_self]

/-- Actual difference of the two original covering lifts. Outside their
true overlap only the irrelevant extension is set to zero. -/
@[expose] def shift (a b:ComplexVectors) (q:Base τ):L τ hτ:=
  if h:q∈baseSet τ hτ a∧q∈baseSet τ hτ b then
    ⟨chart τ hτ b q-chart τ hτ a q,difference_mem τ hτ a b q h.1 h.2⟩ else 0
lemma shift_value (a b:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b):
    (shift τ hτ a b q:ComplexVectors)=chart τ hτ b q-chart τ hτ a q:=by
  simp [shift,ha,hb]
lemma shift_self (a:ComplexVectors) (q:Base τ):shift τ hτ a a q=0:=by
  apply Subtype.ext
  by_cases h:q∈baseSet τ hτ a
  · simp [shift,h]
  · simp [shift,h]
lemma shift_add (a b c:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b) (hc:q∈baseSet τ hτ c):
    shift τ hτ b c q+shift τ hτ a b q=shift τ hτ a c q:=by
  apply Subtype.ext
  simp only [Submodule.coe_add,shift_value τ hτ _ _ q ha hb,
    shift_value τ hτ _ _ q hb hc,shift_value τ hτ _ _ q ha hc]
  abel
lemma shift_locally_constant (a b:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b):
    ∀ᶠr in 𝓝 q,shift τ hτ a b r=shift τ hτ a b q:=by
  have he:(fun r=>(shift τ hτ a b r:ComplexVectors))=ᶠ[𝓝 q]
      (fun r=>chart τ hτ b r-chart τ hτ a r):=by
    filter_upwards [(chart τ hτ a).open_source.mem_nhds ha,
      (chart τ hτ b).open_source.mem_nhds hb] with r hra hrb
    exact shift_value τ hτ a b r hra hrb
  have hv:ContinuousAt (fun r=>(shift τ hτ a b r:ComplexVectors)) q:=
    ((chart τ hτ b).continuousAt hb).sub ((chart τ hτ a).continuousAt ha)
      |>.congr_of_eventuallyEq he.symm
  have hs:ContinuousAt (shift τ hτ a b) q:=
    hv.codRestrict (fun r=>(shift τ hτ a b r).property)
  exact hs ((isOpen_discrete : IsOpen ({shift τ hτ a b q}:Set (L τ hτ))).mem_nhds
    (Set.mem_singleton (shift τ hτ a b q)))

@[expose] def transition (a b:ComplexVectors) (q:Base τ):ℂ:=
  factor τ hτ (shift τ hτ a b q) (chart τ hτ a q)
lemma transition_self (a:ComplexVectors) (q:Base τ):transition τ hτ a a q=1:=by
  rw [transition,shift_self,zero_factor]
lemma transition_nonzero (a b:ComplexVectors) (q:Base τ):transition τ hτ a b q≠0:=
  nonzero τ hτ _ _
lemma transition_comp (a b c:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b) (hc:q∈baseSet τ hτ c):
    transition τ hτ b c q*transition τ hτ a b q=transition τ hτ a c q:=by
  have hs:chart τ hτ a q+(shift τ hτ a b q:ComplexVectors)=chart τ hτ b q:=by
    rw [shift_value τ hτ a b q ha hb]
    abel
  rw [transition,transition,transition,←shift_add τ hτ a b c q ha hb hc,cocycle,hs]
lemma transition_continuous (a b:ComplexVectors):
    ContinuousOn (transition τ hτ a b) (baseSet τ hτ a∩baseSet τ hτ b):=by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  have h:ContinuousAt (fun r=>factor τ hτ (shift τ hτ a b q) (chart τ hτ a r)) q:=
    (holomorphic τ hτ _).continuous.continuousAt.comp q ((chart τ hτ a).continuousAt hq.1)
  apply h.congr_of_eventuallyEq
  filter_upwards [shift_locally_constant τ hτ a b q hq.1 hq.2] with r hr
  simp only [transition,hr]
end PELOriginalPolarizationTransitions318
