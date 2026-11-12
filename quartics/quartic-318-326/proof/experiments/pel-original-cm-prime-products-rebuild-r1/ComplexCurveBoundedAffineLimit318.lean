module
public import ComplexCurveFiniteFilling318
public import ComplexSphereJoukowski318
public section
noncomputable section
namespace ComplexCurveBoundedAffineLimit318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ComplexSphereCharts318
set_option maxHeartbeats 2600000
variable {M:Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M]
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

/-- A bounded AFFINE coordinate of an actual punctured complex-curve map
produces a finite sphere limit in the ORIGINAL source chart. Neither the
map's original value at the puncture nor continuity there is a premise. -/
theorem exists_affine_limit (F:M→OnePoint ℂ) (p:M) (B:ℝ)
    (hpun:∀ᶠq in 𝓝[≠] p,
      ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q ∧ F q∈affine.source ∧ ‖affine (F q)‖≤B) :
    ∃c:ℂ,Tendsto F (𝓝[≠] p) (𝓝 (c:OnePoint ℂ)) := by
  let e:=chartAt ℂ p
  have hp:p∈e.source:=mem_chart_source ℂ p
  have heM:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M:=IsManifold.chart_mem_maximalAtlas p
  have hgM:affine∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=
    IsManifold.subset_maximalAtlas ⟨false,rfl⟩
  have hue:e p∈e.target:=e.map_source hp
  have hi0:e.symm (e p)=p:=e.left_inv hp
  have hto:Tendsto e.symm (𝓝[≠] (e p)) (𝓝[≠] p):=by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · simpa only [hi0] using (e.continuousAt_symm hue).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hue),
        self_mem_nhdsWithin] with z hz hzp
      intro heq
      apply hzp
      calc z=e (e.symm z):=(e.right_inv hz).symm
           _=e p:=congrArg e heq
  have hback:Tendsto e (𝓝[≠] p) (𝓝[≠] (e p)):=by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(e.continuousAt hp).tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e.open_source.mem_nhds hp),
      self_mem_nhdsWithin] with q hq hqp
    intro heq
    exact hqp (e.injOn hq hp heq)
  let H:ℂ→ℂ:=fun z=>affine (F (e.symm z))
  have hd:∀ᶠz in 𝓝[≠] (e p),DifferentiableAt ℂ H z:=by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hue),
      hto.eventually hpun] with z hz hFz
    have hc:=contMDiffAt_of_mem_maximalAtlas hgM hFz.2.1
    have he:=contMDiffAt_symm_of_mem_maximalAtlas heM hz
    have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H z:=hc.comp z (hFz.1.comp z he)
    exact (contMDiffAt_iff_contDiffAt.mp hh).differentiableAt (by simp)
  have hb:∀ᶠz in 𝓝[≠] (e p),‖H z‖≤B:=(hto.eventually hpun).mono (fun z hz=>hz.2.2)
  obtain ⟨G,hGa,hGe,hlim⟩:=BoundedVertexExtension318.analytic_extension hd B hb
  refine ⟨G (e p),?_⟩
  have ht:Tendsto (fun q:M=>(H (e q):OnePoint ℂ)) (𝓝[≠] p) (𝓝 (G (e p):OnePoint ℂ)):=
    OnePoint.continuous_coe.continuousAt.tendsto.comp (hlim.comp hback)
  apply ht.congr'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e.open_source.mem_nhds hp),hpun] with q hq hFq
  change (affine (F (e.symm (e q))):OnePoint ℂ)=F q
  rw [e.left_inv hq]
  exact affine.left_inv hFq.2.1

/-- Actual bounded chart access near a finite puncture set is enough to
CONSTRUCT a global holomorphic filling that changes no other value. -/
theorem exists_holomorphic_filling [T1Space M]
    (F:M→OnePoint ℂ) (S:Set M) (hS:S.Finite)
    (hF:∀q∉S,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q)
    (B:ℝ) (hbound:∀p∈S,∀ᶠq in 𝓝[≠] p,F q∈affine.source ∧ ‖affine (F q)‖≤B) :
    ∃G:M→OnePoint ℂ,ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G ∧
      (∀q∉S,G q=F q) ∧ ∀p∈S,∃c:ℂ,G p=(c:OnePoint ℂ) := by
  classical
  have hlimits:∀p∈S,∃c:ℂ,Tendsto F (𝓝[≠] p) (𝓝 (c:OnePoint ℂ)):=by
    intro p hp
    apply exists_affine_limit F p B
    have hfinite:(S\{p}).Finite:=hS.subset diff_subset
    have hn:(S\{p})ᶜ∈𝓝 p:=hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hbound p hp,eventually_nhdsWithin_of_eventually_nhds hn,self_mem_nhdsWithin]
      with q hq havoid hqp
    have hqS:q∉S:=fun h=>havoid ⟨h,hqp⟩
    exact ⟨hF q hqS,hq⟩
  let c:M→ℂ:=fun p=>if hp:p∈S then (hlimits p hp).choose else 0
  let a:M→OnePoint ℂ:=fun p=>(c p:OnePoint ℂ)
  have ha:∀p∈S,Tendsto F (𝓝[≠] p) (𝓝 (a p)):=by
    intro p hp
    simpa only [a,c,dif_pos hp] using (hlimits p hp).choose_spec
  obtain ⟨hg,hagree⟩:=ComplexCurveFiniteFilling318.holomorphic_fill S hS F a hF ha
  refine ⟨ComplexCurveFiniteFilling318.fill S F a,hg,hagree,?_⟩
  intro p hp
  exact ⟨c p,if_pos hp⟩
end ComplexCurveBoundedAffineLimit318
