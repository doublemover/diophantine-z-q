module
public import PELOriginalCharacterChartLift318
public import ComplexHolomorphicChartInverse318
public section
noncomputable section
namespace PELOriginalCharacterRegularTransition318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318 PELOriginalCharacterTopologicalAtlas318
open PELOriginalCharacterChartLift318 PELOriginalBranchLabels318 PELStabilizerLocusInvariant318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1900000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (i : Fin 4)

/-- The inverse of an actual regular character quotient coordinate is locally the
original quotient projection composed with the unchanged source-chart inverse. -/
theorem inverse_regular_formula (p : UnlevelledBase) (U : Set UnlevelledBase)
    (hU : IsOpen U) (hp : p∈U) (g : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (hs : g.source=toCharacter i '' U)
    (hv : ∀ x∈U,g (toCharacter i x)=chartAt ℂ p x) :
    ∀ᶠ z in 𝓝 (g (toCharacter i p)),
      g.symm z=toCharacter i ((chartAt ℂ p).symm z) := by
  let A := chartAt ℂ p
  have hpA : p∈A.source := mem_chart_source ℂ p
  have hzA : g (toCharacter i p)∈A.target := by
    rw [hv p hp]
    exact A.map_source hpA
  have ht : Tendsto A.symm (𝓝 (g (toCharacter i p))) (𝓝 p) := by
    have hc := A.continuousAt_symm hzA
    simpa only [hv p hp,A.left_inv hpA] using hc.tendsto
  filter_upwards [ht.eventually (hU.mem_nhds hp),A.open_target.mem_nhds hzA] with z hz hzt
  have hg : toCharacter i (A.symm z)∈g.source := by
    rw [hs]
    exact ⟨A.symm z,hz,rfl⟩
  have hval : g (toCharacter i (A.symm z))=z :=
    (hv (A.symm z) hz).trans (A.right_inv hzt)
  calc g.symm z=g.symm (g (toCharacter i (A.symm z))) :=
          congrArg g.symm hval.symm
       _=toCharacter i (A.symm z) := g.left_inv hg

/-- Every retained original chart is holomorphic in any constructed
regular coordinate, on the same quotient point and original source atlas. -/
theorem in_regular_coordinate (p : UnlevelledBase) (U : Set UnlevelledBase)
    (hU : IsOpen U) (hp : p∈U) (g : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (hs : g.source=toCharacter i '' U)
    (hv : ∀ x∈U,g (toCharacter i x)=chartAt ℂ p x)
    (e : OpenPartialHomeomorph (CharacterBase i) ℂ) (he : OriginalChart i e)
    (hpe : toCharacter i p∈e.source) :
    AnalyticAt ℂ (fun z => e (g.symm z)) (g (toCharacter i p)) := by
  let A := chartAt ℂ p
  have hpA : p∈A.source := mem_chart_source ℂ p
  have hzA : g (toCharacter i p)∈A.target := by
    rw [hv p hp]
    exact A.map_source hpA
  have hA := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hzA
  have hL := lift_holomorphic i e he p hpe
  have hLp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (toCharacter i y))
      (A.symm (g (toCharacter i p))) := by
    simpa only [hv p hp,A.left_inv hpA] using hL
  have h := hLp.comp _ hA
  have ha := (contMDiffAt_iff_contDiffAt.mp h).analyticAt
  apply ha.congr
  filter_upwards [inverse_regular_formula i p U hU hp g hs hv] with z hz
  exact congrArg e hz.symm

/-- Transitions of ANY two retained original charts are analytic at every
regular point. The inverse is proved holomorphic, not inferred from a
continuous bijection or assumed nonvanishing derivative. -/
theorem regular_transition (e f : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (hf : OriginalChart i f) (q : (CharacterBase i))
    (hqe : q∈e.source) (hqf : q∈f.source) (hq : q∉exceptionalImage i) :
    AnalyticAt ℂ (fun z => e (f.symm z)) (f q) := by
  obtain ⟨p,rfl⟩ := PELOriginalCharacterTopology318.toCharacter_surjective i q
  have hp : p∉nontrivialStabilizerLocus := fun h => hq ((exceptional_iff i p).mpr h)
  obtain ⟨U,g,hU,hpU,hgs,hgv,hgh⟩ :=
    regular_chart i p hp
  have hqg : toCharacter i p∈g.source := by
    rw [hgs]
    exact ⟨p,hpU,rfl⟩
  let H := g.symm.trans f
  have hxH : g (toCharacter i p)∈H.source := by
    exact ⟨g.map_source hqg,by simpa only [g.left_inv hqg] using hqf⟩
  have hH : AnalyticAt ℂ H (g (toCharacter i p)) :=
    in_regular_coordinate i p U hU hpU g hgs hgv f hf hqf
  have hInv := ComplexHolomorphicChartInverse318.inverse_analytic H hxH hH
  have hInv' : AnalyticAt ℂ (fun z => g (f.symm z))
      (f (toCharacter i p)) := by
    simpa only [H,OpenPartialHomeomorph.coe_trans,Function.comp_apply,g.left_inv hqg,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,OpenPartialHomeomorph.symm_symm] using hInv
  have hE := in_regular_coordinate i p U hU hpU g hgs hgv e he hqe
  have hE' : AnalyticAt ℂ (fun z => e (g.symm z))
      (g (f.symm (f (toCharacter i p)))) := by
    simpa only [f.left_inv hqf] using hE
  have ha := hE'.comp hInv'
  apply ha.congr
  have ht := f.continuousAt_symm (f.map_source hqf)
  have hnear : ∀ᶠ z in 𝓝 (f (toCharacter i p)),f.symm z∈g.source := by
    have ht' : Tendsto f.symm (𝓝 (f (toCharacter i p)))
        (𝓝 (toCharacter i p)) := by
      simpa only [f.left_inv hqf] using ht.tendsto
    exact ht'.eventually (g.open_source.mem_nhds hqg)
  filter_upwards [hnear] with z hz
  exact congrArg e (g.left_inv hz)
end PELOriginalCharacterRegularTransition318
