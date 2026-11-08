module
public import AdmissiblePeriodProjection318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public section
noncomputable section
open Filter Set Topology
open scoped Manifold ContDiff
namespace AdmissibleAnalyticSections318
open ModularArithmeticCoordinates318 ThreeArithmeticQuotient318
open AdmissibleJLocalHomeomorph318 OpenJLocalComparison318
set_option maxHeartbeats 500000

/-- A continuous local right inverse of an analytic scalar function with
nonzero derivative is the actual analytic inverse germ. -/
lemma analytic_of_right_inverse {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hn : deriv f x ≠ 0)
    (hg : Tendsto g (𝓝 (f x)) (𝓝 x))
    (hfg : ∀ᶠ z in 𝓝 (f x), f (g z) = z) : AnalyticAt ℂ g (f x) := by
  let r := hf.hasStrictDerivAt.localInverse f (deriv f x) x hn
  have hl : ∀ᶠ y in 𝓝 x, r (f y) = y :=
    hf.hasStrictDerivAt.eventually_left_inverse hn
  have he : r =ᶠ[𝓝 (f x)] g := by
    filter_upwards [hg.eventually hl, hfg] with z hz hright
    rwa [hright] at hz
  exact (hf.analyticAt_localInverse hn).congr he

/-- The original quotient covering's own chosen local inverse, not a newly
selected period branch from equality of j values alone. -/
@[expose] def inverseSection (tau : Locus) : OpenPartialHomeomorph Source Locus :=
  AdmissibleQuotientCover318.localHomeomorph.localInverseAt tau

lemma inverseSection_symm (tau : Locus) :
    (inverseSection tau).symm = sourceProjection :=
  AdmissibleQuotientCover318.localHomeomorph.localInverseAt_symm tau

lemma inverseSection_center (tau : Locus) :
    inverseSection tau (sourceProjection tau) = tau :=
  AdmissibleQuotientCover318.localHomeomorph.localInverseAt_apply_self

lemma inverseSection_projection (tau : Locus) {q : Source}
    (hq : q ∈ (inverseSection tau).source) :
    sourceProjection (inverseSection tau q) = q :=
  AdmissibleQuotientCover318.localHomeomorph.apply_localInverseAt_of_mem hq

lemma j_inverseSection (tau : Locus) {q : Source}
    (hq : q ∈ (inverseSection tau).source) :
    j ((inverseSection tau q).val : ℂ) = sourceComplexJ q := by
  simp only [j, UpperHalfPlane.ofComplex_apply]
  exact (sourceComplexJ_projection (inverseSection tau q)).symm.trans
    (congrArg sourceComplexJ (inverseSection_projection tau hq))

/-- Actual natural period coordinates of this inverse section in the
specified genuine-j source chart. -/
@[expose] def inverseCoordinates (tau : Locus) (q : Source) (z : ℂ) : ℂ :=
  ((inverseSection tau ((AdmissibleJComplexAtlas318.localChart q).symm z)).val : ℂ)

/-- Every point in an actual inverse branch has analytic natural period
coordinates. Nonvanishing of genuine j' is consumed at that exact period. -/
theorem inverse_coordinates_analytic (tau : Locus) (q : Source)
    (hq : q ∈ (inverseSection tau).source) :
    AnalyticAt ℂ (inverseCoordinates tau q) (sourceComplexJ q) := by
  have ht : Tendsto (AdmissibleJComplexAtlas318.localChart q).symm
      (𝓝 (sourceComplexJ q)) (𝓝 q) := by
    simpa only [AdmissibleJComplexAtlas318.localChart_apply] using
      (AdmissibleJComplexAtlas318.localChart q).tendsto_symm
        (AdmissibleJComplexAtlas318.localChart_center q)
  have hs := (inverseSection tau).continuousAt hq
  have hg : Tendsto (inverseCoordinates tau q) (𝓝 (sourceComplexJ q))
      (𝓝 ((inverseSection tau q).val : ℂ)) :=
    locus_complex_embedding.continuous.continuousAt.tendsto.comp (hs.tendsto.comp ht)
  have hj : ∀ᶠ z in 𝓝 (sourceComplexJ q),
      sourceComplexJ ((AdmissibleJComplexAtlas318.localChart q).symm z) = z := by
    simpa only [AdmissibleJComplexAtlas318.localChart_apply] using
      (AdmissibleJComplexAtlas318.localChart q).eventually_right_inverse'
        (AdmissibleJComplexAtlas318.localChart_center q)
  have hright : ∀ᶠ z in 𝓝 (sourceComplexJ q), j (inverseCoordinates tau q z) = z := by
    filter_upwards [ht.eventually ((inverseSection tau).open_source.mem_nhds hq), hj]
      with z hz hjz
    exact (j_inverseSection tau hz).trans hjz
  have ha := analytic_of_right_inverse (f := j) (g := inverseCoordinates tau q)
    (j_analyticAt (inverseSection tau q).val)
    (ActualJImmersion318.deriv_j_ne_zero (inverseSection tau q).val
      (inverseSection tau q).property)
    (by simpa only [j_inverseSection tau hq] using hg)
    (by simpa only [j_inverseSection tau hq] using hright)
  simpa only [j_inverseSection tau hq] using ha

local instance : Nonempty Locus := AdmissiblePeriodProjection318.locus_nonempty

/-- The same actual covering inverse is analytic throughout its open domain
for the independently natural period atlas, not just for a transported atlas. -/
theorem inverseSection_analytic (tau : Locus) :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (inverseSection tau) (inverseSection tau).source := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff.mpr
  refine ⟨(inverseSection tau).continuousAt hq, ?_⟩
  change ContDiffWithinAt ℂ ω (inverseCoordinates tau q) _
    (AdmissibleJComplexAtlas318.localChart q q)
  rw [AdmissibleJComplexAtlas318.localChart_apply]
  exact (inverse_coordinates_analytic tau q hq).contDiffAt.contDiffWithinAt

/-- The original covering partial homeomorphism, with analytic proofs in
both directions and unchanged maps and domains. -/
@[expose] def localBiholomorph (tau : Locus) :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) Locus Source ω := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  refine {
    toPartialEquiv := (inverseSection tau).symm.toPartialEquiv
    open_source := (inverseSection tau).open_target
    open_target := (inverseSection tau).open_source
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := inverseSection_analytic tau }
  change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (inverseSection tau).symm (inverseSection tau).target
  rw [inverseSection_symm]
  exact AdmissiblePeriodProjection318.sourceProjection_analytic.contMDiffOn

/-- The genuine period-to-orbit projection is locally biholomorphic with
respect to the natural period complex structure and the genuine-j quotient atlas. -/
theorem sourceProjection_localDiffeomorph :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω sourceProjection := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  intro tau
  have hm : tau ∈ (localBiholomorph tau).source :=
    AdmissibleQuotientCover318.localHomeomorph.self_mem_localInverseAt_target
  have h := (localBiholomorph tau).isLocalDiffeomorphAt hm
  have he : (localBiholomorph tau : Locus → Source) = sourceProjection :=
    inverseSection_symm tau
  rw [he] at h
  exact h

end AdmissibleAnalyticSections318
