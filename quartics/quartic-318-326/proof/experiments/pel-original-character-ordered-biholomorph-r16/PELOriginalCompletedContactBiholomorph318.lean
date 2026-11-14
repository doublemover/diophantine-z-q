module
public import PELOriginalCompletedContactHolomorphy318
public import PELOriginalContactTargetDensity318
public import PELOriginalBaseCompact318
public import DenseTargetOpenComparison318
public import ComplexCurveOpenMapping318
public section
noncomputable section
namespace PELOriginalCompletedContactBiholomorph318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 PELOriginalCompletedContactGeneric318
open FourRootNormalizedPointCharts318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
local instance : T2Space (Completed branches):=FourRootCompletedHausdorff318.hausdorff branches
local instance : ChartedSpace ℂ (Completed branches):=
  FourRootCompletedComplexAtlas318.chartedSpace branches branches_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed branches):=
  FourRootCompletedComplexAtlas318.complex_manifold branches branches_injective
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold

/-- Openness at every original branch and infinity point follows from
actual whole holomorphy and injectivity on the dense OPEN regular locus.
No boundary openness or completed bijection is inserted as an assumption. -/
theorem open_map : IsOpenMap completedMap := by
  apply ComplexCurveOpenMapping318.isOpenMap completedMap
    PELOriginalCompletedContactHolomorphy318.holomorphic RegularSource
    PELOriginalContactRegularDensity318.regular_open
    PELOriginalContactRegularDensity318.regular_dense
  intro x hx y hy hxy
  exact generic_fiber_unique x y hxy (regular_maps_generic x hx)

/-- Actual whole genus-five source identified with the independently
normalized four-root target, INCLUDING all ramified fibers and all eight
infinity points. The fixed map and original topology/atlas are retained;
compactness and independently proved target Hausdorffness extend the
actual dense generic-fiber bijection, not a cardinality coincidence. -/
@[expose] def comparison : UnlevelledBase≃ₜCompleted branches:=
  DenseTargetOpenComparison318.homeomorph completedMap
    PELOriginalCompletedContactContinuity318.continuous open_map Generic
    PELOriginalContactTargetDensity318.generic_dense generic_covered generic_fiber_unique
lemma comparison_value (p:UnlevelledBase):comparison p=completedMap p:=rfl
lemma forward_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω comparison:=
  PELOriginalCompletedContactHolomorphy318.holomorphic
lemma inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω comparison.symm:=
  ComplexCurveHomeomorphInverse318.inverse comparison forward_holomorphic

/-- Same original manuscript base on the WHOLE curve, not just on a
nonempty open or up to an unmarked projective automorphism. -/
theorem actual_projection (p:UnlevelledBase):
    FourRootNormalizedPointCharts318.projection branches (comparison p)=normalizedMap p:=
  projection_commutes p

@[expose] def fiberEquiv (q:OnePoint ℂ):
    {p:UnlevelledBase//normalizedMap p=q} ≃
      {p:Completed branches//FourRootNormalizedPointCharts318.projection branches p=q} where
  toFun p:=⟨comparison p.val,(actual_projection p.val).trans p.property⟩
  invFun p:=⟨comparison.symm p.val,by
    rw [←actual_projection,comparison.apply_symm_apply]
    exact p.property⟩
  left_inv p:=Subtype.ext (comparison.symm_apply_apply p.val)
  right_inv p:=Subtype.ext (comparison.apply_symm_apply p.val)

/-- The original infinity fiber consists of the actual eight distinct
normalized sign triples, with no collapsed product of elliptic branches. -/
@[expose] def targetInfinityEquiv :
    {p:Completed branches//FourRootNormalizedPointCharts318.projection branches p=∞} ≃ InfinitySigns where
  toFun p:=match p with
    | ⟨.inr s,_⟩=>s
    | ⟨.inl q,h⟩=>False.elim (OnePoint.coe_ne_infty q.val.1 h)
  invFun s:=⟨.inr s,rfl⟩
  left_inv p:=by
    rcases p with ⟨p|s,h⟩
    · exact False.elim (OnePoint.coe_ne_infty p.val.1 h)
    · rfl
  right_inv _:=rfl
@[expose] def infinityEquiv : {p:UnlevelledBase//normalizedMap p=∞} ≃ InfinitySigns:=
  (fiberEquiv ∞).trans targetInfinityEquiv

theorem infinity_card : Nat.card {p:UnlevelledBase//normalizedMap p=∞}=8 := by
  rw [Nat.card_congr infinityEquiv]
  exact FourRootNormalizedOverlap318.infinity_card
end PELOriginalCompletedContactBiholomorph318
