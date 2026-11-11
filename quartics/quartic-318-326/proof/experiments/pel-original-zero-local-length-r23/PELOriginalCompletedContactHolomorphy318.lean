module
public import FourRootNativeGermHolomorphy318
public import PELOriginalCompletedContactContinuity318
public section
noncomputable section
namespace PELOriginalCompletedContactHolomorphy318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalContactBranchParameters318 PELOriginalContactParameterLocality318
open PELOriginalCompletedContactPoints318 PELOriginalContactRootExtensions318
open PELOriginalCompletedContactContinuity318
open FourRootNormalizedPointCharts318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
local instance : ChartedSpace ℂ (Completed branches):=
  FourRootCompletedComplexAtlas318.chartedSpace branches branches_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed branches):=
  FourRootCompletedComplexAtlas318.complex_manifold branches branches_injective
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold

lemma regular (p:UnlevelledBase) (hp:p∈RegularSource):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω completedMap p:=by
  have ht:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(regularGerm p hp x).val.1) p:=by
    apply (PELOriginalContactRootHolomorphy318.base_holomorphic p hp).congr_of_eventuallyEq
    filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
    simp only [regularGerm,dif_pos hx]
  have hz:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(regularGerm p hp x).val.2 k) p:=by
    intro k
    apply (PELOriginalContactRootHolomorphy318.roots_holomorphic p hp k).congr_of_eventuallyEq
    filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
    simp only [regularGerm,dif_pos hx]
  exact (FourRootNativeGermHolomorphy318.finite branches branches_injective
    (regularGerm p hp) p ht hz).congr_of_eventuallyEq (regular_map_germ p hp)

lemma finite_parameter (p:UnlevelledBase) (hp:p∈PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w=>completedMap (source (finiteParameter p hp j h) w)) 0:=by
  let g:=PELOriginalContactFiniteMapGerm318.germ p hp j h
  have hv:=PELOriginalContactFiniteMapGerm318.value p hp j h
  have ht:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.1) 0:=by
    have ha:AnalyticAt ℂ (fun w:ℂ=>branches j+w^2) 0:=analyticAt_const.add (analyticAt_id.pow 2)
    apply (contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt).congr_of_eventuallyEq
    exact hv.mono (fun w hw=>congrArg Prod.fst hw)
  have hz:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.2 k) 0:=by
    intro k
    apply (contMDiffAt_iff_contDiffAt.mpr (finiteRoots_analytic p hp j h k).contDiffAt).congr_of_eventuallyEq
    exact hv.mono (fun w hw=>congrArg (fun v:ℂ×(Fin 4→ℂ)=>v.2 k) hw)
  exact (FourRootNativeGermHolomorphy318.finite branches branches_injective g 0 ht hz).
    congr_of_eventuallyEq (PELOriginalContactFiniteMapGerm318.map_germ p hp j h)

lemma infinity_parameter (p:UnlevelledBase) (hp:p∈PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (h:normalizedMap p=∞):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w=>completedMap (source (infinityParameter p hp h) w)) 0:=by
  let g:=PELOriginalContactInfinityMapGerm318.germ p hp h
  have hv:=PELOriginalContactInfinityMapGerm318.value p hp h
  have hu:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.1) 0:=by
    apply (contMDiffAt_iff_contDiffAt.mpr (PELOriginalContactInfinityMapGerm318.u_analytic p hp h).contDiffAt).
      congr_of_eventuallyEq
    exact hv.mono (fun w hw=>congrArg Prod.fst hw)
  have hs:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.2 k) 0:=by
    intro k
    apply (contMDiffAt_iff_contDiffAt.mpr (PELOriginalContactInfinityMapGerm318.ratios_analytic p hp h k).contDiffAt).
      congr_of_eventuallyEq
    exact hv.mono (fun w hw=>congrArg (fun v:ℂ×(Fin 4→ℂ)=>v.2 k) hw)
  have hg0:g 0=FourRootInfinityGraph318.center branches (infinityCenter p hp h):=
    PELOriginalContactInfinityMapGerm318.germ_zero p hp h
  exact (FourRootNativeGermHolomorphy318.infinity branches branches_injective g 0
    (infinityCenter p hp h) hg0 hu hs).congr_of_eventuallyEq
      (PELOriginalContactInfinityMapGerm318.map_germ p hp h)

/-- Full holomorphy of the SAME fixed completed contact map, with the
ORIGINAL genus-five source atlas and INDEPENDENT normalized target atlas.
Both finite branch neighborhoods and every infinity branch are included.
The actual local inverse source coordinates discharge all extension steps. -/
theorem holomorphic:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω completedMap:=by
  intro p
  by_cases hr:p∈RegularSource
  · exact regular p hr
  · have hp:=ramified_of_not_regular p hr
    by_cases hi:normalizedMap p=∞
    · exact PELOriginalContactParameterLocality318.transfer (infinityParameter p hp hi)
        completedMap (infinity_parameter p hp hi)
    · let j:=branchIndex p hr hi
      have hj:=branchIndex_value p hr hi
      exact PELOriginalContactParameterLocality318.transfer (finiteParameter p hp j hj)
        completedMap (finite_parameter p hp j hj)
end PELOriginalCompletedContactHolomorphy318
