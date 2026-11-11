module
public import AnalyticZeroLocusChart318
public import Mathlib.Analysis.Analytic.Constructions
public section
noncomputable section
namespace AnalyticEmbeddedCurveChart318
open Set Filter
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Build an actual open chart in an independently inherited ambient
subspace, from a genuine parametrization and FULL ambient local inverse.
The coordinate is a specified continuous ambient function, not transported
from a different curve. -/
theorem exists_chart (S:Set E) (p:S) (axis:E→ℂ) (haxis:Continuous axis)
    (Z:ℂ→S) (hZ:AnalyticAt ℂ (fun z=>(Z z).val) (axis p.val))
    (hcenter:Z (axis p.val)=p) (hleft:∀z,axis (Z z).val=z)
    (hright:∀ᶠq in 𝓝 p.val,q∈S→(Z (axis q)).val=q) :
    ∃e:OpenPartialHomeomorph S ℂ,p∈e.source ∧
      (∀q,e q=axis q.val) ∧
      AnalyticOnNhd ℂ (fun z=>(e.symm z).val) e.target := by
  obtain ⟨V,hV,hVo,hVp⟩:=eventually_nhds_iff.mp hright
  have ht:Tendsto (fun z=>(Z z).val) (𝓝 (axis p.val)) (𝓝 p.val):=by
    simpa only [hcenter] using hZ.continuousAt.tendsto
  have hn:∀ᶠz in 𝓝 (axis p.val),(Z z).val∈V ∧
      AnalyticAt ℂ (fun w=>(Z w).val) z:=
    (ht.eventually (hVo.mem_nhds hVp)).and hZ.eventually_analyticAt
  obtain ⟨U,hU,hUo,hUp⟩:=eventually_nhds_iff.mp hn
  have hcont:ContinuousOn Z U:=by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have ha:ContinuousOn (fun z=>(Z z).val) U:=
      fun z hz=>(hU z hz).2.continuousAt.continuousWithinAt
    exact (continuousOn_iff_continuous_domRestrict.mp ha).subtype_mk _
  let e:OpenPartialHomeomorph S ℂ:={
    toFun:=fun q=>axis q.val
    invFun:=Z
    source:={q|q.val∈V ∧ axis q.val∈U}
    target:=U
    map_source':=fun _ hq=>hq.2
    map_target':=by
      intro z hz
      exact ⟨(hU z hz).1,(hleft z).symm ▸ hz⟩
    left_inv':=fun q hq=>Subtype.ext (hV q.val hq.1 q.property)
    right_inv':=fun z _=>hleft z
    open_source:=(hVo.preimage continuous_subtype_val).inter
      (hUo.preimage (haxis.comp continuous_subtype_val))
    open_target:=hUo
    continuousOn_toFun:=(haxis.comp continuous_subtype_val).continuousOn
    continuousOn_invFun:=hcont}
  exact ⟨e,⟨hVp,hUp⟩,fun _=>rfl,fun z hz=>(hU z hz).2⟩
end AnalyticEmbeddedCurveChart318
