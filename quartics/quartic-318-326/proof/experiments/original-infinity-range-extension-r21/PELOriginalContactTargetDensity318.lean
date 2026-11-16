module
public import PELOriginalCompletedContactGeneric318
public import FourRootCompletedHausdorff318
public section
noncomputable section
namespace PELOriginalContactTargetDensity318
open Set Filter
open scoped Topology
open PELOriginalCommonContactBase318 PELOriginalCompletedContactGeneric318
open FourRootNormalizedPointCharts318 FourCharacterRootRecombination318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches

/-- Every actual finite target branch is approached by its independent
signed square graph through genuinely generic target points. -/
lemma finite_branch_closure (p:FinitePoints branches) (j:Fin 4) (hp:p.val.1=branches j):
    (Sum.inl p:Completed branches)∈closure Generic := by
  obtain ⟨Z,hZ0,hZt,hZj,hZa,hZi⟩:=
    FourRootFiniteBranchGraph318.parametrization branches branches_injective j p hp
  have ht:ContinuousAt (fun w=>(Z w).val.1) 0:=by
    have he:(fun w=>(Z w).val.1)=(fun w:ℂ=>branches j+w^2):=funext hZt
    rw [he]
    fun_prop
  have hz:ContinuousAt (fun w=>(Z w).val.2) 0:=
    continuousAt_pi.mpr (fun k=>(hZa k).continuousAt)
  have hc:ContinuousAt Z 0:=(ht.prodMk hz).subtype_mk _
  have hf:ContinuousAt (fun w=>finiteChart branches (Z w)) 0:=
    (FourRootGluedTopology318.finiteChart_continuous branches).continuousAt.comp hc
  have hlim:Tendsto (fun w=>finiteChart branches (Z w)) (𝓝[≠] (0:ℂ)) (𝓝 (Sum.inl p)):=by
    simpa only [hZ0,finiteChart] using hf.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [FourRootPuncturedRegularity318.finite branches branches_injective j] with w hw
  refine ⟨Z w,rfl,?_⟩
  rw [hZt]
  exact hw

/-- Each of the eight independent infinity sign triples is approached
through its actual normalized u-chart; no infinity fiber is collapsed. -/
lemma infinity_closure (s:InfinitySigns):
    (Sum.inr s:Completed branches)∈closure Generic := by
  obtain ⟨Z,hZ0,hZu,hZa,hZi⟩:=FourRootInfinityGraph318.parametrization branches s
  have ht:ContinuousAt (fun w=>(Z w).val.1) 0:=by
    have he:(fun w=>(Z w).val.1)=id:=funext hZu
    rw [he]
    exact continuousAt_id
  have hz:ContinuousAt (fun w=>(Z w).val.2) 0:=
    continuousAt_pi.mpr (fun k=>(hZa k).continuousAt)
  have hc:ContinuousAt Z 0:=(ht.prodMk hz).subtype_mk _
  have hf:ContinuousAt (fun w=>infinityChart branches (Z w)) 0:=
    (FourRootGluedTopology318.infinityChart_continuous branches).continuousAt.comp hc
  have hlim:Tendsto (fun w=>infinityChart branches (Z w)) (𝓝[≠] (0:ℂ)) (𝓝 (Sum.inr s)):=by
    have he:infinityChart branches (Z 0)=Sum.inr s:=by
      rw [hZ0]
      exact infinityChart_zero branches s
    simpa only [he] using hf.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [FourRootPuncturedRegularity318.infinity branches,self_mem_nhdsWithin] with w hw hn
  have hne:(Z w).val.1≠0:=by rw [hZu];exact hn
  refine ⟨(toFinite branches ⟨Z w,hne⟩).val,infinityChart_nonzero branches (Z w) hne,?_⟩
  change denominator branches (branches 0+((Z w).val.1^2)⁻¹)≠0
  rw [hZu,show branches 0=0 from rfl,zero_add]
  exact hw

/-- Density is proved in the explicitly GLUED independent topology by
actual local equation graphs, not borrowed from the original source. -/
theorem generic_dense : Dense Generic := by
  intro p
  rcases p with p|s
  · by_cases hD:denominator branches p.val.1≠0
    · exact subset_closure ⟨p,rfl,hD⟩
    · have hex:∃j:Fin 4,p.val.1=branches j:=by
        by_contra hh
        have hn:∀j,p.val.1≠branches j:=by simpa using hh
        exact hD ((FourRootPuncturedRegularity318.denominator_ne_iff branches p.val.1).mpr hn)
      obtain ⟨j,hj⟩:=hex
      exact finite_branch_closure p j hj
  · exact infinity_closure s
end PELOriginalContactTargetDensity318
