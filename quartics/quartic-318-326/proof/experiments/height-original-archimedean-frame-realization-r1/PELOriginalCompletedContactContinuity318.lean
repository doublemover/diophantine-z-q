module
public import PELOriginalContactInfinityMapGerm318
public import PELOriginalContactRegularDensity318
public section
noncomputable section
namespace PELOriginalCompletedContactContinuity318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalContactBranchParameters318 PELOriginalContactParameterLocality318
open PELOriginalCompletedContactPoints318 PELOriginalContactRootExtensions318
open FourRootNormalizedPointCharts318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold

@[expose] def regularGerm (p:UnlevelledBase) (hp:p∈RegularSource) (x:UnlevelledBase):FinitePoints branches:=
  if hx:x∈RegularSource then ⟨(base x,roots x),roots_square x hx⟩
  else ⟨(base p,roots p),roots_square p hp⟩
lemma regular_continuous (p:UnlevelledBase) (hp:p∈RegularSource):
    ContinuousAt (regularGerm p hp) p:=by
  have ht:ContinuousAt base p:=(PELOriginalContactRootHolomorphy318.base_holomorphic p hp).continuousAt
  have hz:ContinuousAt roots p:=continuousAt_pi.mpr
    (fun k=>(PELOriginalContactRootHolomorphy318.roots_holomorphic p hp k).continuousAt)
  apply tendsto_subtype_rng.mpr
  apply (ht.prodMk hz).congr_of_eventuallyEq
  filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
  simp only [regularGerm,dif_pos hx]
lemma regular_map_germ (p:UnlevelledBase) (hp:p∈RegularSource):
    completedMap=ᶠ[𝓝 p] (fun x=>finiteChart branches (regularGerm p hp x)):=by
  filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
  rw [completedMap_regular x hx,regularGerm,dif_pos hx]
  rfl
lemma continuousAt_regular (p:UnlevelledBase) (hp:p∈RegularSource):ContinuousAt completedMap p:=
  ((FourRootGluedTopology318.finiteChart_continuous branches).continuousAt.comp
    (regular_continuous p hp)).congr_of_eventuallyEq (regular_map_germ p hp)

/-- The actual original parameter and its actual inverse identify a
WHOLE source neighborhood. Continuity along the parameter therefore gives
continuity at the unchanged original point, not only on a chosen arc. -/
lemma transfer {p:UnlevelledBase} {B:ℂ→OnePoint ℂ}
    (P:SquareParametrization p B)
    (hf:ContinuousAt (fun w=>completedMap (source P w)) 0):ContinuousAt completedMap p:=by
  have hc:ContinuousAt (coordinate P) p:=(coordinate_holomorphic P).continuousAt
  have hf':ContinuousAt (fun w=>completedMap (source P w)) (coordinate P p):=by
    rw [coordinate_zero]
    exact hf
  apply (hf'.comp hc).congr_of_eventuallyEq
  filter_upwards [source_coordinate P] with x hx
  exact (congrArg completedMap hx).symm

/-- The fixed complete map is continuous into the INDEPENDENT topology
glued from the two actual normalized affine charts. In particular all
eight infinity branches retain neighborhoods containing finite points;
no source topology or accidental disjoint-sum topology is transported. -/
theorem continuous : Continuous completedMap:=by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hr:p∈RegularSource
  · exact continuousAt_regular p hr
  · have hp:=ramified_of_not_regular p hr
    by_cases hi:normalizedMap p=∞
    · exact transfer (infinityParameter p hp hi)
        (PELOriginalContactInfinityMapGerm318.along_source_continuous p hp hi)
    · let j:=branchIndex p hr hi
      have hj:=branchIndex_value p hr hi
      exact transfer (finiteParameter p hp j hj)
        (PELOriginalContactFiniteMapGerm318.along_source_continuous p hp j hj)
end PELOriginalCompletedContactContinuity318
