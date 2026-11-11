module
public import PELOriginalAllLevelProjectiveMap318
public import ComplexProjectiveComplexAtlas318
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public section
noncomputable section
namespace PELOriginalAllLevelHolomorphicMap318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Filter Topology
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalAllLevelProjectiveMap318 ComplexProjectiveQuotientTopology318
open ComplexProjectiveRatioCharts318 ComplexProjectiveComplexAtlas318
open scoped Manifold ContDiff
variable (τ:ℂ) (hτ:0<τ.im) (n:ℕ)
local instance discretePeriods:DiscreteTopology (P τ):=PELOriginalPeriodLattice318.original_discrete τ hτ
abbrev Target (n:ℕ):=Space (Label (n+2))
abbrev TargetModel (n:ℕ):=Model (Label (n+2)) (0:Label (n+2))
local instance targetTopology:TopologicalSpace (Target n):=topology (Label (n+2))
local instance targetCharts:ChartedSpace (TargetModel n) (Target n):=
  ComplexProjectiveComplexAtlas318.chartedSpace (Label (n+2)) 0
local instance targetManifold:IsManifold 𝓘(ℂ,(TargetModel n)) ω (Target n):=
  ComplexProjectiveComplexAtlas318.complex_manifold (Label (n+2)) 0
local instance sourceCharts:ChartedSpace ComplexVectors (Base τ):=
  PELComplexPeriodSurface318.surfaceCharts τ hτ
local instance sourceManifold:IsManifold 𝓘(ℂ,ComplexVectors) ω (Base τ):=
  PELComplexPeriodSurface318.surface_manifold τ hτ

lemma coverVector_continuous:Continuous (coverVector τ hτ n):=by
  apply continuous_pi
  intro r
  exact (PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) r).continuous
lemma covering_continuous:Continuous (coveringMap τ hτ n):=
  continuous_mk (Label (n+2)) (coverVector τ hτ n) (coverVector_continuous τ hτ n)
    (coverVector_nonzero τ hτ n)
lemma original_continuous:Continuous (projectiveMap τ hτ n):=by
  have hp:IsQuotientMap (projection (P τ)):=isQuotientMap_quotient_mk'
  apply hp.continuous_iff.mpr
  simpa only [Function.comp_apply,original_covering_square] using covering_continuous τ hτ n

@[expose] def ratioVector (j:Label (n+2))(z:ComplexVectors):(TargetModel n):=
  coordinates (Label (n+2)) 0 j (fun i=>value τ hτ (n+2) i.val z/value τ hτ (n+2) j z)
lemma actual_ratio (j:Label (n+2))(z:ComplexVectors):
    ComplexProjectiveComplexAtlas318.localChart (Label (n+2)) 0 j (coveringMap τ hτ n z)=
      ratioVector τ hτ n j z:=rfl
lemma ratio_differentiable (j:Label (n+2))(z:ComplexVectors)
    (hz:value τ hτ (n+2) j z≠0):DifferentiableAt ℂ (ratioVector τ hτ n j) z:=by
  have hd:DifferentiableAt ℂ (fun w:ComplexVectors=>fun i:{i:Label (n+2) //i≠j}=>
      value τ hτ (n+2) i.val w/value τ hτ (n+2) j w) z:=by
    apply differentiableAt_pi.mpr
    intro i
    exact (PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) i.val z).div
      (PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) j z) hz
  exact (coordinates (Label (n+2)) 0 j).toContinuousLinearEquiv.differentiableAt.comp z hd
lemma chart_maximal (j:Label (n+2)):
    ComplexProjectiveComplexAtlas318.localChart (Label (n+2)) 0 j∈
      IsManifold.maximalAtlas 𝓘(ℂ,(TargetModel n)) ω (Target n):=
  IsManifold.subset_maximalAtlas ⟨j,rfl⟩

/-- Genuine holomorphy into the independently constructed complex projective target:
local ratios are differentiated only where the chosen actual homogeneous
coordinate is nonzero, and the inverse target chart is genuinely analytic. -/
theorem covering_holomorphic:
    MDifferentiable 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,(TargetModel n)) (coveringMap τ hτ n):=by
  intro z
  have hn:=coverVector_nonzero τ hτ n z
  have hx:∃j:Label (n+2),value τ hτ (n+2) j z≠0:=by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨j,hj⟩:=hx
  let e:=ComplexProjectiveComplexAtlas318.localChart (Label (n+2)) 0 j
  have hsource:coveringMap τ hτ n z∈e.source:=
    (mk_mem_domain (Label (n+2)) j _ _).mpr hj
  have hr:MDifferentiableAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,(TargetModel n))
      (ratioVector τ hτ n j) z:=
    mdifferentiableAt_iff_differentiableAt.mpr (ratio_differentiable τ hτ n j z hj)
  have hi:MDifferentiableAt 𝓘(ℂ,(TargetModel n)) 𝓘(ℂ,(TargetModel n))
      e.symm (ratioVector τ hτ n j z):=
    (contMDiffAt_symm_of_mem_maximalAtlas (chart_maximal n j)
      (by simpa only [actual_ratio] using e.map_source hsource)).mdifferentiableAt (by simp)
  apply (hi.comp z hr).congr_of_eventuallyEq
  have he:∀ᶠw in 𝓝 z,value τ hτ (n+2) j w≠0:=
    (PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) j).continuous.continuousAt.eventually_ne hj
  filter_upwards [he] with w hw
  have hsw:coveringMap τ hτ n w∈e.source:=(mk_mem_domain (Label (n+2)) j _ _).mpr hw
  change coveringMap τ hτ n w=e.symm (ratioVector τ hτ n j w)
  rw [←actual_ratio]
  exact (e.left_inv hsw).symm

/-- Holomorphy of the SAME original projective map on the SAME original
period surface, descended through its actual local covering charts. -/
theorem original_holomorphic:
    MDifferentiable 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,(TargetModel n)) (projectiveMap τ hτ n):=by
  intro p
  obtain ⟨a,rfl⟩:=quotient_surjective (P τ) p
  let e:=DiscreteComplexPeriodAtlas318.localChart (P τ) a
  have hp:projection (P τ) a∈e.source:=localChart_center (P τ) a
  have hv:e (projection (P τ) a)=a:=
    (quotient_localHomeomorph (P τ)).localInverseAt_apply_self
  have hl:MDifferentiableAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,(TargetModel n))
      (projectiveMap τ hτ n∘e.symm) a:=by
    apply (covering_holomorphic τ hτ n a).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z=>by
      change projectiveMap τ hτ n (e.symm z)=coveringMap τ hτ n z
      rw [localChart_symm,original_covering_square])
  have hc:MDifferentiableAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors)
      e (projection (P τ) a):=
    (contMDiffAt_of_mem_maximalAtlas (DiscreteComplexPeriodMaps318.chart_maximal (P τ) a) hp).mdifferentiableAt (by simp)
  have hl':MDifferentiableAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,(TargetModel n))
      (projectiveMap τ hτ n∘e.symm) (e (projection (P τ) a)):=by rwa [hv]
  apply (hl'.comp _ hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply,e.left_inv hq]

lemma actual_target_dimension:
    Module.finrank ℂ (TargetModel n)=(n+2)^2-1:=by
  simp [TargetModel,ComplexProjectiveComplexAtlas318.Model,ComplexProjectiveRatioCharts318.Affine,
    Module.finrank_pi,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
    Label,Fintype.card_prod,pow_two]
end PELOriginalAllLevelHolomorphicMap318
