module
public import ComplexCurveHomeomorphInverse318
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
namespace ComplexCurveOpenMapping318
open Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 3000000
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- Injectivity on a DENSE OPEN original interior rules out a constant
germ anywhere on the given complex curve. The proof uses actual source
charts, not an assumed genus or a transported complex structure. -/
theorem not_locally_constant (F : M → N) (U : Set M) (hU : IsOpen U)
    (hd : Dense U) (hinj : InjOn F U) (p : M) :
    ¬ ∀ᶠ q in 𝓝 p,F q=F p := by
  intro hc
  obtain ⟨W,hW,hWo,hpW⟩ := eventually_nhds_iff.mp hc
  obtain ⟨q,hqW,hqU⟩ := hd.inter_open_nonempty W hWo ⟨p,hpW⟩
  let e := chartAt ℂ q
  have hq : q∈e.source := mem_chart_source ℂ q
  have hi : ContinuousAt e.symm (e q) := e.continuousAt_symm (e.map_source hq)
  have hnear : ∀ᶠ z in 𝓝 (e q),z∈e.target ∧ e.symm z∈W ∩ U := by
    refine (e.open_target.mem_nhds (e.map_source hq)).and (hi.eventually ?_)
    simpa only [e.left_inv hq] using (hWo.inter hU).mem_nhds ⟨hqW,hqU⟩
  have hf : ∀ᶠ z in 𝓝[≠] (e q),False := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear,self_mem_nhdsWithin] with z hz hne
    have heq : e.symm z=q := hinj hz.2.2 hqU ((hW _ hz.2.1).trans (hW q hqW).symm)
    apply hne
    calc z=e (e.symm z) := (e.right_inv hz.1).symm
         _=e q := congrArg e heq
  obtain ⟨z,hz⟩ := hf.exists
  exact hz

/-- Original-curve local open mapping from the genuine complex analytic
open-mapping theorem. Only a locally constant germ is excluded. -/
theorem image_mem_nhds (F : M → N) (p : M)
    (hF : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F p)
    (hn : ¬ ∀ᶠ q in 𝓝 p,F q=F p) (A : Set M) (hA : A∈𝓝 p) :
    F '' A∈𝓝 (F p) := by
  let e := chartAt ℂ p
  let g := chartAt ℂ (F p)
  have hp : p∈e.source := mem_chart_source ℂ p
  have hgp : F p∈g.source := mem_chart_source ℂ (F p)
  have heM : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := IsManifold.chart_mem_maximalAtlas p
  have hgM : g∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N := IsManifold.chart_mem_maximalAtlas (F p)
  have hep : e.symm (e p)=p := e.left_inv hp
  let H : ℂ → ℂ := fun z => g (F (e.symm z))
  have hF' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (e.symm (e p)) := by simpa only [hep] using hF
  have hg' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g (F (e.symm (e p))) := by
    simpa only [hep] using contMDiffAt_of_mem_maximalAtlas hgM hgp
  have hHC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H (e p) :=
    hg'.comp (e p) (hF'.comp (e p)
      (contMDiffAt_symm_of_mem_maximalAtlas heM (e.map_source hp)))
  have hHA : AnalyticAt ℂ H (e p) := (contMDiffAt_iff_contDiffAt.mp hHC).analyticAt
  have hH0 : H (e p)=g (F p) := by dsimp [H]; rw [hep]
  have hopen : 𝓝 (H (e p))≤Filter.map H (𝓝 (e p)) := by
    apply hHA.eventually_constant_or_nhds_le_map_nhds.resolve_left
    intro hc
    apply hn
    filter_upwards [e.open_source.mem_nhds hp,(e.continuousAt hp).eventually hc,
      hF.continuousAt.eventually (g.open_source.mem_nhds hgp)] with q hq hconst hFq
    apply g.injOn hFq hgp
    simpa only [H,e.left_inv hq,hep] using hconst
  have hi : ContinuousAt e.symm (e p) := e.continuousAt_symm (e.map_source hp)
  have hiA : ∀ᶠ z in 𝓝 (e p),e.symm z∈A := hi.eventually (by simpa only [hep] using hA)
  have hcF : ContinuousAt (fun z => F (e.symm z)) (e p) := hF'.continuousAt.comp hi
  let T : Set ℂ := {z | z∈e.target ∧ e.symm z∈A ∧ F (e.symm z)∈g.source}
  have hT : T∈𝓝 (e p) :=
    (e.open_target.mem_nhds (e.map_source hp)).and (hiA.and
      (hcF.eventually (by simpa only [hep] using g.open_source.mem_nhds hgp)))
  have hHT : H '' T∈𝓝 (g (F p)) := by
    rw [←hH0]
    apply hopen
    change H ⁻¹' (H '' T)∈𝓝 (e p)
    exact Filter.mem_of_superset hT (fun z hz => ⟨z,hz,rfl⟩)
  filter_upwards [g.open_source.mem_nhds hgp,(g.continuousAt hgp).eventually hHT] with y hy hym
  obtain ⟨z,hz,hzy⟩ := hym
  exact ⟨e.symm z,hz.2.1,g.injOn hz.2.2 hy hzy⟩

/-- Holomorphy and dense OPEN interior injectivity give openness of the
same global map, including every seam and filled vertex. -/
theorem isOpenMap (F : M → N)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (U : Set M) (hU : IsOpen U) (hd : Dense U) (hinj : InjOn F U) : IsOpenMap F := by
  intro A hA
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨p,hp,rfl⟩
  exact image_mem_nhds F p (hF p) (not_locally_constant F U hU hd hinj p) A (hA.mem_nhds hp)
end ComplexCurveOpenMapping318
