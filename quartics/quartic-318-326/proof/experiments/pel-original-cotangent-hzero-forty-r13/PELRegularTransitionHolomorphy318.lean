module
public import PELOriginalChartLift318
public import ComplexHolomorphicChartInverse318
public section
noncomputable section
namespace PELRegularTransitionHolomorphy318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318
open PELOriginalChartLift318 PELOriginalBranchLabels318 PELStabilizerLocusInvariant318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1900000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The inverse of an actual regular quotient coordinate is locally the
original quotient projection composed with the unchanged source-chart inverse. -/
theorem inverse_regular_formula (p : UnlevelledBase) (U : Set UnlevelledBase)
    (hU : IsOpen U) (hp : p∈U) (g : OpenPartialHomeomorph MaximalBase ℂ)
    (hs : g.source=PELOriginalMaximalQuotient318.projection '' U)
    (hv : ∀ x∈U,g (PELOriginalMaximalQuotient318.projection x)=chartAt ℂ p x) :
    ∀ᶠ z in 𝓝 (g (PELOriginalMaximalQuotient318.projection p)),
      g.symm z=PELOriginalMaximalQuotient318.projection ((chartAt ℂ p).symm z) := by
  let A := chartAt ℂ p
  have hpA : p∈A.source := mem_chart_source ℂ p
  have hzA : g (PELOriginalMaximalQuotient318.projection p)∈A.target := by
    rw [hv p hp]
    exact A.map_source hpA
  have ht : Tendsto A.symm (𝓝 (g (PELOriginalMaximalQuotient318.projection p))) (𝓝 p) := by
    have hc := A.continuousAt_symm hzA
    simpa only [hv p hp,A.left_inv hpA] using hc.tendsto
  filter_upwards [ht.eventually (hU.mem_nhds hp),A.open_target.mem_nhds hzA] with z hz hzt
  have hg : PELOriginalMaximalQuotient318.projection (A.symm z)∈g.source := by
    rw [hs]
    exact ⟨A.symm z,hz,rfl⟩
  have hval : g (PELOriginalMaximalQuotient318.projection (A.symm z))=z :=
    (hv (A.symm z) hz).trans (A.right_inv hzt)
  calc g.symm z=g.symm (g (PELOriginalMaximalQuotient318.projection (A.symm z))) :=
          congrArg g.symm hval.symm
       _=PELOriginalMaximalQuotient318.projection (A.symm z) := g.left_inv hg

/-- Every retained original chart is holomorphic in any constructed
regular coordinate, on the same quotient point and original source atlas. -/
theorem in_regular_coordinate (p : UnlevelledBase) (U : Set UnlevelledBase)
    (hU : IsOpen U) (hp : p∈U) (g : OpenPartialHomeomorph MaximalBase ℂ)
    (hs : g.source=PELOriginalMaximalQuotient318.projection '' U)
    (hv : ∀ x∈U,g (PELOriginalMaximalQuotient318.projection x)=chartAt ℂ p x)
    (e : OpenPartialHomeomorph MaximalBase ℂ) (he : OriginalChart e)
    (hpe : PELOriginalMaximalQuotient318.projection p∈e.source) :
    AnalyticAt ℂ (fun z => e (g.symm z)) (g (PELOriginalMaximalQuotient318.projection p)) := by
  let A := chartAt ℂ p
  have hpA : p∈A.source := mem_chart_source ℂ p
  have hzA : g (PELOriginalMaximalQuotient318.projection p)∈A.target := by
    rw [hv p hp]
    exact A.map_source hpA
  have hA := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hzA
  have hL := lift_holomorphic e he p hpe
  have hLp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (PELOriginalMaximalQuotient318.projection y))
      (A.symm (g (PELOriginalMaximalQuotient318.projection p))) := by
    simpa only [hv p hp,A.left_inv hpA] using hL
  have h := hLp.comp _ hA
  have ha := (contMDiffAt_iff_contDiffAt.mp h).analyticAt
  apply ha.congr
  filter_upwards [inverse_regular_formula p U hU hp g hs hv] with z hz
  exact congrArg e hz.symm

/-- Transitions of ANY two retained original charts are analytic at every
regular point. The inverse is proved holomorphic, not inferred from a
continuous bijection or assumed nonvanishing derivative. -/
theorem regular_transition (e f : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart e) (hf : OriginalChart f) (q : MaximalBase)
    (hqe : q∈e.source) (hqf : q∈f.source) (hq : q∉branchImage) :
    AnalyticAt ℂ (fun z => e (f.symm z)) (f q) := by
  obtain ⟨p,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  have hp : p∉nontrivialStabilizerLocus := fun h => hq ((branch_image_iff p).mpr h)
  obtain ⟨U,g,hU,hpU,hgs,hgv,hgh⟩ :=
    PELRegularQuotientChart318.exists_regular_chart p hp
  have hqg : PELOriginalMaximalQuotient318.projection p∈g.source := by
    rw [hgs]
    exact ⟨p,hpU,rfl⟩
  let H := g.symm.trans f
  have hxH : g (PELOriginalMaximalQuotient318.projection p)∈H.source := by
    exact ⟨g.map_source hqg,by simpa only [g.left_inv hqg] using hqf⟩
  have hH : AnalyticAt ℂ H (g (PELOriginalMaximalQuotient318.projection p)) :=
    in_regular_coordinate p U hU hpU g hgs hgv f hf hqf
  have hInv := ComplexHolomorphicChartInverse318.inverse_analytic H hxH hH
  have hInv' : AnalyticAt ℂ (fun z => g (f.symm z))
      (f (PELOriginalMaximalQuotient318.projection p)) := by
    simpa only [H,OpenPartialHomeomorph.coe_trans,Function.comp_apply,g.left_inv hqg,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,OpenPartialHomeomorph.symm_symm] using hInv
  have hE := in_regular_coordinate p U hU hpU g hgs hgv e he hqe
  have hE' : AnalyticAt ℂ (fun z => e (g.symm z))
      (g (f.symm (f (PELOriginalMaximalQuotient318.projection p)))) := by
    simpa only [f.left_inv hqf] using hE
  have ha := hE'.comp hInv'
  apply ha.congr
  have ht := f.continuousAt_symm (f.map_source hqf)
  have hnear : ∀ᶠ z in 𝓝 (f (PELOriginalMaximalQuotient318.projection p)),f.symm z∈g.source := by
    have ht' : Tendsto f.symm (𝓝 (f (PELOriginalMaximalQuotient318.projection p)))
        (𝓝 (PELOriginalMaximalQuotient318.projection p)) := by
      simpa only [f.left_inv hqf] using ht.tendsto
    exact ht'.eventually (g.open_source.mem_nhds hqg)
  filter_upwards [hnear] with z hz
  exact congrArg e (g.left_inv hz)
end PELRegularTransitionHolomorphy318
