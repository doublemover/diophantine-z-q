module
public import PELOriginalLiteralBranchParameters318
public import PELOriginalStripEndpointMatching318
public import SimpleBranchCrossingPaths318
public section
noncomputable section
namespace PELOriginalBranchCrossingArcs318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalLiteralBranchParameters318 SimpleBranchCrossingPaths318
open LegendreHalfPlaneAnalyticSheets318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- Actual original lifts of both polynomial crossing paths, with common
right endpoint and DISTINCT left endpoints. One radius controls complete
paths inside an arbitrarily prescribed branch-coordinate neighborhood.
The lift maps and their continuity are constructed from the original
invertible branch parameter, not assumed local monodromy data. -/
theorem exists_crossing (p:CharacterBase i) (a:ℝ)
    (ha:normalizedMap i p=(a:ℂ))
    (hb:(a:ℂ)=0 ∨ (a:ℂ)=1 ∨ (a:ℂ)=branchParameter i)
    (V:Set ℂ) (hV:V∈𝓝 (0:ℂ)) :
    ∃(s:ℝ)(hs:0<s),∃F:Bool→ℝ→CharacterBase i,
      (∀upper t,t∈Icc 0 1 → rootArc upper s t∈V) ∧
      (∀upper t,t∈Icc 0 1 → ContinuousAt (F upper) t) ∧
      (∀upper t,t∈Icc 0 1 → normalizedMap i (F upper t)=(baseArc a upper s t:OnePoint ℂ)) ∧
      F true 0=F false 0 ∧ F true 1≠F false 1 ∧
      (∀upper,∃e:BaseFiber i upper,∀(t:ℝ)(ht:t∈Ioo 0 1),
        sheet i upper e ⟨baseArc a upper s t,interior_halfplane a upper s t hs ht⟩=F upper t) := by
  let P:=PELOriginalLiteralBranchParameters318.finite i p (a:ℂ) ha hb
  let G:ℂ→CharacterBase i:=fun w=>P.chart.symm (P.inverseChange w)
  let U:Set ℂ:={w | w∈V ∧ P.inverseChange w∈P.chart.target ∧
    normalizedMap i (G w)=(a+w^2:ℂ) ∧ P.changeMap (P.inverseChange w)=w ∧
    AnalyticAt ℂ P.inverseChange w}
  have hU:U∈𝓝 (0:ℂ):=by
    filter_upwards [hV,P.projection,P.right_inverse,P.inverse_analytic.eventually_analyticAt]
      with w hw hp hr hk
    exact ⟨hw,hp.1,hp.2,hr,hk⟩
  obtain ⟨s,hs,hpath⟩:=exists_small_crossing hU
  let F:Bool→ℝ→CharacterBase i:=fun upper t=>G (rootArc upper s t)
  have hG:∀w∈U,ContinuousAt G w:=by
    intro w hw
    exact (P.chart.continuousAt_symm hw.2.1).comp hw.2.2.2.2.continuousAt
  have hcont:∀upper t,t∈Icc 0 1 → ContinuousAt (F upper) t:=by
    intro upper t ht
    exact (hG _ (hpath upper t ht)).comp (rootArc_continuous upper s).continuousAt
  have hproj:∀upper t,t∈Icc 0 1 →
      normalizedMap i (F upper t)=(baseArc a upper s t:OnePoint ℂ):=by
    intro upper t ht
    exact (hpath upper t ht).2.2.1
  have hinj:InjOn G U:=by
    intro w hw z hz he
    have hk:P.inverseChange w=P.inverseChange z:=by
      have hh:=congrArg P.chart he
      simpa only [G,P.chart.right_inv hw.2.1,P.chart.right_inv hz.2.1] using hh
    have hh:=congrArg P.changeMap hk
    simpa only [hw.2.2.2.1,hz.2.2.2.1] using hh
  refine ⟨s,hs,F,fun upper t ht=>(hpath upper t ht).1,hcont,hproj,?_,?_,?_⟩
  · change G (rootArc true s 0)=G (rootArc false s 0)
    rw [rootArc_start,rootArc_start]
  · intro he
    have hh:=hinj (hpath true 1 ⟨by norm_num,le_rfl⟩)
      (hpath false 1 ⟨by norm_num,le_rfl⟩) he
    exact endpoints_distinct s hs hh.symm
  · intro upper
    apply PELOriginalHalfPlaneArcSheets318.one_sheet i upper (baseArc a upper s) (F upper)
    · exact (baseArc_continuous a upper s).continuousOn
    · intro t ht
      exact (hcont upper t ⟨ht.1.le,ht.2.le⟩).continuousWithinAt
    · exact fun t ht=>interior_halfplane a upper s t hs ht
    · exact fun t ht=>hproj upper t ⟨ht.1.le,ht.2.le⟩
end PELOriginalBranchCrossingArcs318
