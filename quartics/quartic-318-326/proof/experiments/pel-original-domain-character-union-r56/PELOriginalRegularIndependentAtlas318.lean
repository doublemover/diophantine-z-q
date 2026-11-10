module
public import PELOriginalRegularCoordinateHolomorphy318
public import LegendreGlobalHolomorphicDifferential318
public section
noncomputable section
namespace PELOriginalRegularIndependentAtlas318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalRegularCoverPatches318 PELOriginalGluedLegendreMap318
open PELOriginalGluedLegendreFibers318 PELOriginalRegularLegendreHomeomorph318
open LegendreLiteralCompletedAtlas318
variable (i : Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
abbrev Completed := LegendrePlaneOverlap318.CompletedPlane (branchParameter i)

/-- Embed the literal regular target into its independent completed atlas,
retaining the native x=t-shift convention. -/
@[expose] def targetEmbedding (p : Target i) : Completed i :=
  LegendrePlaneOverlap318.finiteChart (branchParameter i)
    ((literalFiniteHomeomorph (branchParameter i)).symm p.val)
lemma target_open : IsOpenEmbedding (targetEmbedding i) := by
  have hreg : IsOpen {p : NormalizedLegendreFieldPoints318.FinitePoints (branchParameter i) |
      p.val.1≠0 ∧ p.val.1≠1 ∧ p.val.1≠branchParameter i} :=
    (isOpen_ne (by fun_prop) continuous_const).inter
      ((isOpen_ne (by fun_prop) continuous_const).inter
        (isOpen_ne (by fun_prop) continuous_const))
  exact (LegendrePlaneOverlap318.finite_open (branchParameter i)).comp
    ((literalFiniteHomeomorph (branchParameter i)).symm.isOpenEmbedding.comp hreg.isOpenEmbedding_subtypeVal)

@[expose] def sourcePartial : OpenPartialHomeomorph (CharacterBase i) (Target i) :=
  (homeomorph i).toOpenPartialHomeomorph.lift_openEmbedding
    (regular_open i).isOpenEmbedding_subtypeVal
@[expose] def comparison : OpenPartialHomeomorph (CharacterBase i) (Completed i) :=
  (sourcePartial i).trans ((target_open i).toOpenPartialHomeomorph (targetEmbedding i))

lemma sourcePartial_value (x : Regular i) : sourcePartial i x.val=homeomorph i x :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _
lemma comparison_value (x : Regular i) :
    comparison i x.val=targetEmbedding i (homeomorph i x) := by
  change targetEmbedding i (sourcePartial i x.val)=_
  rw [sourcePartial_value]
lemma comparison_source (x : CharacterBase i) (hx : x∈Regular i) : x∈(comparison i).source := by
  exact ⟨⟨⟨x,hx⟩,Set.mem_univ _,rfl⟩,Set.mem_univ _⟩
lemma comparison_finite (x : Regular i) :
    comparison i x.val=LegendrePlaneOverlap318.finiteChart (branchParameter i)
      ((literalFiniteEquiv (branchParameter i)).symm (finiteMap i x)) :=
  comparison_value i x
lemma comparison_scheme (x : Regular i) :
    LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i) (comparison i x.val)=
      NormalizedLegendreFieldPoints318.schemeEquiv (branchParameter i) (some (finiteMap i x)) := by
  rw [comparison_finite,finite_scheme,Equiv.apply_symm_apply]

local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (Completed i):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed i):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- Actual global regular forward holomorphy between BOTH independently
constructed manifold atlases. This consumes actual original source
coordinate holomorphy and the literal completed target chart, not a
manifold structure transported through the regular homeomorphism. -/
theorem holomorphic (x : CharacterBase i) (hx : x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) x := by
  let p := (literalFiniteEquiv (branchParameter i)).symm (finiteMap i ⟨x,hx⟩)
  let e := LegendreCompletedComplexAtlas318.finiteChart (branchParameter i) p
  have he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed i) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inl p,rfl⟩
  have hp : comparison i x∈e.source := by
    rw [comparison_finite i ⟨x,hx⟩]
    exact ⟨p,LegendreFiniteComplexAtlas318.chart_center (branchParameter i) p,rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((comparison i).continuousAt (comparison_source i x hx)).continuousWithinAt,?_⟩
  have hh:=PELOriginalRegularCoordinateHolomorphy318.coordinates_holomorphic i x hx
  have hn:Regular i∈𝓝 x := (regular_open i).mem_nhds hx
  have hcoord : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (e ∘ comparison i) x := by
    rcases LegendreFiniteComplexAtlas318.chart_axis (branchParameter i) p with ha|ha
    · apply (hh.1.sub_const (NormalizedLegendreProjectiveModel318.shift (branchParameter i))).congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      change e (comparison i y)=(coordinates i y).1-NormalizedLegendreProjectiveModel318.shift (branchParameter i)
      rw [comparison_finite i ⟨y,hy⟩]
      rw [LegendreCompletedComplexAtlas318.finite_apply,ha,literalFinite_inverse]
      all_goals rfl
    · apply hh.2.congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      change e (comparison i y)=(coordinates i y).2
      rw [comparison_finite i ⟨y,hy⟩]
      rw [LegendreCompletedComplexAtlas318.finite_apply,ha,literalFinite_inverse]
      all_goals rfl
  exact hcoord.contMDiffWithinAt

/-- Actual regular inverse holomorphy follows from the SAME partial
homeomorphism and its proved forward holomorphy. No derivative hypothesis
or inverse-analyticity assertion is added. -/
theorem inverse_holomorphic (x : CharacterBase i) (hx : x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm (comparison i x) :=
  ComplexCurvePartialInverse318.inverse_at (comparison i) x (comparison_source i x hx)
    (holomorphic i x hx)

theorem actual_regular_biholomorphic (x : CharacterBase i) (hx : x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) x ∧
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm (comparison i x) :=
  ⟨holomorphic i x hx,inverse_holomorphic i x hx⟩
end PELOriginalRegularIndependentAtlas318
