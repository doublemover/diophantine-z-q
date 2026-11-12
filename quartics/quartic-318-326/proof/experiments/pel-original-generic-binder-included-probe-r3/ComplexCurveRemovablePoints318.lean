module
public import ComplexSphereJoukowski318
public import Mathlib.Analysis.Complex.RemovableSingularity
public section
noncomputable section
namespace ComplexCurveRemovablePoints318
open Set Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2800000
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- Removability for a continuous map between the GIVEN complex curves.
The source and target charts are their original maximal-atlas charts;
there is no change of complex structure at the exceptional point. -/
theorem removable_at (F : M → N) {p : M} (hF : ContinuousAt F p)
    (hpun : ∀ᶠ q in 𝓝[≠] p,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F p := by
  let e := chartAt ℂ p
  let g := chartAt ℂ (F p)
  have hp : p∈e.source := mem_chart_source ℂ p
  have hFp : F p∈g.source := mem_chart_source ℂ (F p)
  have heM : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := IsManifold.chart_mem_maximalAtlas p
  have hgM : g∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N := IsManifold.chart_mem_maximalAtlas (F p)
  have hue : e p∈e.target := e.map_source hp
  have hi : ContinuousAt e.symm (e p) := e.continuousAt_symm hue
  have hi0 : e.symm (e p)=p := e.left_inv hp
  have hto : Tendsto e.symm (𝓝[≠] (e p)) (𝓝[≠] p) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · simpa only [hi0] using hi.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hue),
        self_mem_nhdsWithin] with z hz hzp
      intro heq
      apply hzp
      calc z=e (e.symm z) := (e.right_inv hz).symm
           _=e p := congrArg e heq
  let H : ℂ → ℂ := fun z => (g : N → ℂ) (F (e.symm z))
  have hcF : ContinuousAt (fun z => F (e.symm z)) (e p) := by
    apply ContinuousAt.comp _ hi
    simpa only [hi0] using hF
  have hcH : ContinuousAt H (e p) := by
    change ContinuousAt ((g : N → ℂ) ∘ (fun z => F (e.symm z))) (e p)
    have hgAt : ContinuousAt (g : N → ℂ) (F (e.symm (e p))) := by
      simpa only [hi0] using g.continuousAt hFp
    exact ContinuousAt.comp (f := fun z : ℂ => F (e.symm z))
      (g := (g : N → ℂ)) (x := e p) hgAt hcF
  have hnear : ∀ᶠ z in 𝓝 (e p), z∈e.target ∧ F (e.symm z)∈g.source :=
    (show ∀ᶠ z in 𝓝 (e p), z ∈ e.target from e.open_target.mem_nhds hue).and
      (hcF.eventually (by
        change g.source ∈ 𝓝 (F (e.symm (e p)))
        rw [hi0]
        exact g.open_source.mem_nhds hFp))
  have hdiff : ∀ᶠ z in 𝓝[≠] (e p),DifferentiableAt ℂ H z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear,hto.eventually hpun] with z hz hq
    have hc := contMDiffAt_of_mem_maximalAtlas hgM hz.2
    have he := contMDiffAt_symm_of_mem_maximalAtlas heM hz.1
    have hh : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H z :=
      hc.comp z (hq.comp z he)
    exact (contMDiffAt_iff_contDiffAt.mp hh).differentiableAt (by simp)
  have hHA : AnalyticAt ℂ H (e p) :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcH
  have hHC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H (e p) :=
    contMDiffAt_iff_contDiffAt.mpr hHA.contDiffAt
  have heC := contMDiffAt_of_mem_maximalAtlas heM hp
  have hgC := contMDiffAt_symm_of_mem_maximalAtlas hgM (g.map_source hFp)
  have hvalue : H (e p)=g (F p) := by dsimp [H]; rw [hi0]
  have hgC' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g.symm (H (e p)) := hvalue.symm ▸ hgC
  apply (hgC'.comp p (hHC.comp p heC)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp,hF.eventually (g.open_source.mem_nhds hFp)] with q hq hFq
  change F q=g.symm (g (F (e.symm (e q))))
  rw [e.left_inv hq,g.left_inv hFq]

/-- Finitely many remaining vertex points are removable once the actual
continuous descended map is holomorphic off those points. -/
theorem holomorphic_of_finite_exception [T1Space M] (F : M → N) (hF : Continuous F)
    (S : Set M) (hS : S.Finite)
    (hhol : ∀ p∉S,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F p) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F := by
  intro p
  apply removable_at F hF.continuousAt
  have hfinite : (S\{p}).Finite := hS.subset diff_subset
  have havoid : (S\{p})ᶜ∈𝓝 p := hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds havoid,self_mem_nhdsWithin] with q hq hqp
  apply hhol q
  intro hqS
  exact hq ⟨hqS,hqp⟩
end ComplexCurveRemovablePoints318
