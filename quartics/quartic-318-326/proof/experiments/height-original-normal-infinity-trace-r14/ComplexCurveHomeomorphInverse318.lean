module
public import ComplexCurveFiniteFilling318
public import ComplexHolomorphicChartInverse318
public section
noncomputable section
namespace ComplexCurveHomeomorphInverse318
open Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2600000
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- The inverse of an actual holomorphic homeomorphism of the GIVEN
complex curves is holomorphic. Nonvanishing derivative is not supplied:
it follows through the existing injective-chart inverse theorem. -/
theorem inverse_at (h : M ≃ₜ N) (p : M)
    (hh : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h p) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.symm (h p) := by
  let e := chartAt ℂ p
  let g := chartAt ℂ (h p)
  have hp : p∈e.source := mem_chart_source ℂ p
  have hhp : h p∈g.source := mem_chart_source ℂ (h p)
  have heM : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := IsManifold.chart_mem_maximalAtlas p
  have hgM : g∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N := IsManifold.chart_mem_maximalAtlas (h p)
  have hep : e.symm (e p)=p := e.left_inv hp
  let K : OpenPartialHomeomorph ℂ ℂ := (e.symm.trans h.toOpenPartialHomeomorph).trans g
  have hk : e p∈K.source := by
    refine ⟨⟨e.map_source hp,Set.mem_univ _⟩,?_⟩
    change h (e.symm (e p))∈g.source
    simpa only [hep] using hhp
  have hv : K (e p)=g (h p) := by
    change g (h (e.symm (e p)))=g (h p)
    rw [hep]
  have hh' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h (e.symm (e p)) := by
    simpa only [hep] using hh
  have hg' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g (h (e.symm (e p))) := by
    simpa only [hep] using contMDiffAt_of_mem_maximalAtlas hgM hhp
  have hKC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω K (e p) :=
    hg'.comp (f := fun z : ℂ => h (e.symm z)) (e p) (hh'.comp (e p)
      (contMDiffAt_symm_of_mem_maximalAtlas heM (e.map_source hp)))
  have hKA : AnalyticAt ℂ K (e p) :=
    (contMDiffAt_iff_contDiffAt.mp hKC).analyticAt
  have hIA := ComplexHolomorphicChartInverse318.inverse_analytic K hk hKA
  rw [hv] at hIA
  have hIC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω K.symm (g (h p)) :=
    contMDiffAt_iff_contDiffAt.mpr hIA.contDiffAt
  have hleft : K.symm (g (h p))=e p := by rw [←hv]; exact K.left_inv hk
  have heC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm (K.symm (g (h p))) := by
    rw [hleft]
    exact contMDiffAt_symm_of_mem_maximalAtlas heM (e.map_source hp)
  have hgC := contMDiffAt_of_mem_maximalAtlas hgM hhp
  apply (heC.comp (h p) (hIC.comp (h p) hgC)).congr_of_eventuallyEq
  have hnear : ∀ᶠ q in 𝓝 (h p),h.symm q∈e.source :=
    h.symm.continuous.continuousAt.eventually (by simpa using e.open_source.mem_nhds hp)
  filter_upwards [g.open_source.mem_nhds hhp,hnear] with q hq heq
  change h.symm q=e.symm (e (h.symm (g.symm (g q))))
  rw [g.left_inv hq,e.left_inv heq]

/-- Global inverse holomorphy on the SAME original complex structures. -/
theorem inverse (h : M ≃ₜ N) (hh : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.symm := by
  intro q
  simpa using inverse_at h (h.symm q) (hh (h.symm q))
end ComplexCurveHomeomorphInverse318
