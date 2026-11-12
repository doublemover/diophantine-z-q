module
public import LegendrePeriodScalingPoints318
public section
noncomputable section
namespace LegendrePeriodScalingHolomorph318
open ComplexAffineFreeTranslation318 LegendrePeriodScalingPoints318 Set Filter
open scoped Topology Manifold ContDiff
variable (L:AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)] (u:ℂˣ)
variable (hA:NormalizedLegendreProjectiveModel318.A l=(u:ℂ)^4*OriginalPeriodProjectiveModel318.A L)
variable (hB:NormalizedLegendreProjectiveModel318.B l=(u:ℂ)^6*OriginalPeriodProjectiveModel318.B L)
local instance : ChartedSpace ℂ (OriginalPeriodPlaneOverlap318.CompletedPlane L):=
  OriginalPeriodCompletedComplexAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane L):=
  OriginalPeriodCompletedComplexAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane l):=
  LegendreCompletedComplexAtlas318.chartedSpace l
local instance : IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane l):=
  LegendreCompletedComplexAtlas318.complex_manifold l

private lemma transfer (e:OpenPartialHomeomorph (OriginalPeriodPlaneOverlap318.CompletedPlane L) ℂ)
    (he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane L))
    (p:OriginalPeriodPlaneOverlap318.CompletedPlane L) (hp:p∈e.source)
    (hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun z=>equivalence L l u hA hB (e.symm z)) (e p)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (equivalence L l u hA hB) p := by
  apply (hh.comp p (contMDiffAt_of_mem_maximalAtlas he hp)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  change equivalence L l u hA hB q=equivalence L l u hA hB (e.symm (e q))
  rw [e.left_inv hq]

/-- Holomorphy in the independently constructed native finite charts,
including all finite branch points. Both native target axes are allowed. -/
lemma finite_holomorphic (p:OriginalPeriodFiniteComplexAtlas318.Plane L) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (equivalence L l u hA hB)
      (OriginalPeriodPlaneOverlap318.finiteChart L p) := by
  let e:=OriginalPeriodCompletedComplexAtlas318.finiteChart L p
  let q:=OriginalPeriodPlaneOverlap318.finiteChart L p
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane L):=
    IsManifold.subset_maximalAtlas ⟨Sum.inl p,rfl⟩
  have hp:q∈e.source:=⟨p,OriginalPeriodFiniteComplexAtlas318.chart_center L p,rfl⟩
  apply transfer L l u hA hB e he q hp
  have ht:e q∈(OriginalPeriodFiniteComplexAtlas318.chart L p).target:=e.map_source hp
  have ha:=OriginalPeriodFiniteComplexAtlas318.inverse_analytic L p (e q) ht
  let g:=fun z=>finite L l u hA hB ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z)
  have hg:AnalyticAt ℂ (fun z=>(g z).val) (e q):=
    (analyticAt_const.mul (analyticAt_fst.comp ha)).prod
      (analyticAt_const.mul (analyticAt_snd.comp ha))
  have hh:=LegendreNativeGermHolomorphy318.finite l g (e q) hg
  convert hh using 1
  funext z
  rw [OriginalPeriodCompletedComplexAtlas318.finite_inverse,finite_value]

/-- Holomorphy at infinity is proved in actual U,V coordinates, with
U/u,V/u³, and in particular at the actual native origin. -/
lemma infinity_holomorphic (p:OriginalPeriodPlaneOverlap318.InfinityPlane L) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (equivalence L l u hA hB)
      (OriginalPeriodPlaneOverlap318.infinityChart L p) := by
  let e:=OriginalPeriodCompletedComplexAtlas318.infinityChart L p
  let q:=OriginalPeriodPlaneOverlap318.infinityChart L p
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane L):=
    IsManifold.subset_maximalAtlas ⟨Sum.inr p,rfl⟩
  have hp:q∈e.source:=⟨p,OriginalPeriodInfinityComplexAtlas318.chart_center L p,rfl⟩
  apply transfer L l u hA hB e he q hp
  have ht:e q∈(OriginalPeriodInfinityComplexAtlas318.chart L p).target:=e.map_source hp
  have ha:=OriginalPeriodInfinityComplexAtlas318.inverse_analytic L p (e q) ht
  let g:=fun z=>infinity L l u hA hB ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z)
  have hg:AnalyticAt ℂ (fun z=>(g z).val) (e q):=
    ((analyticAt_fst.comp ha).div_const _).prod ((analyticAt_snd.comp ha).div_const _)
  have hh:=LegendreNativeGermHolomorphy318.infinity l g (e q) hg
  convert hh using 1
  funext z
  rw [OriginalPeriodCompletedComplexAtlas318.infinity_inverse,infinity_value]

theorem holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (equivalence L l u hA hB) := by
  intro p
  rcases OriginalPeriodPlaneOverlap318.chart_cover L p with ⟨q,rfl⟩|⟨q,rfl⟩
  · exact finite_holomorphic L l u hA hB q
  · exact infinity_holomorphic L l u hA hB q

/-- Concrete scaling on both affine charts gives an actual global
biholomorphism. Equality of j is only a producer of the coefficients,
never a substitute for these chart and gluing proofs. -/
@[expose] def comparison : OriginalPeriodPlaneOverlap318.CompletedPlane L≃ₜ
    LegendrePlaneOverlap318.CompletedPlane l :=
  (equivalence L l u hA hB).toHomeomorphOfContinuousOpen
    (holomorphic L l u hA hB).continuous
    (ComplexCurveOpenMapping318.isOpenMap _ (holomorphic L l u hA hB)
      Set.univ isOpen_univ dense_univ (equivalence L l u hA hB).injective.injOn)
theorem biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison L l u hA hB) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison L l u hA hB).symm :=
  ⟨holomorphic L l u hA hB,
    ComplexCurveHomeomorphInverse318.inverse _ (holomorphic L l u hA hB)⟩
end LegendrePeriodScalingHolomorph318
