module
public import PELOriginalCompletedInfinityAtlas318
public import ComplexCurveOpenMapping318
public section
noncomputable section
namespace PELOriginalCompletedBiholomorph318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalRegularCoverPatches318 PELOriginalCompletedLegendreBijection318
open PELOriginalCompletedIndependentMap318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (PELOriginalCompletedIndependentMap318.Target i):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (PELOriginalCompletedIndependentMap318.Target i):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- All points of the ORIGINAL complex character curve map
holomorphically into the INDEPENDENT completed Legendre atlas. The cases
use actual regular sheets and derived finite/infinity branch extensions. -/
theorem holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (map i) := by
  intro p
  by_cases hr:p∈Regular i
  · exact regular_holomorphic i p hr
  · have hb:Branch i (PELOriginalNormalizedDoubleCover318.normalizedMap i p):=by
      by_contra hn
      exact hr ((regular_iff i p).mpr hn)
    rcases hb with h|h|h|h
    · exact PELOriginalCompletedInfinityAtlas318.holomorphic i p h
    · exact finite_branch_holomorphic i 0 p h
    · exact finite_branch_holomorphic i 1 p h
    · exact finite_branch_holomorphic i 2 p h

/-- Openness follows from actual holomorphy and injectivity. No target
Hausdorff premise or compact-bijection shortcut is needed. -/
theorem open_map : IsOpenMap (map i) :=
  ComplexCurveOpenMapping318.isOpenMap (map i) (holomorphic i)
    Set.univ isOpen_univ dense_univ (bijective i).1.injOn

/-- The SAME fixed full scheme-point equivalence is a genuine global
homeomorphism, including all four branches. No complex structure on the
target is transported from the source. -/
@[expose] def comparison : CharacterBase i≃ₜPELOriginalCompletedIndependentMap318.Target i :=
  (equivalence i).toHomeomorphOfContinuousOpen (holomorphic i).continuous (open_map i)
lemma comparison_value (p:CharacterBase i) : comparison i p=map i p:=rfl
lemma forward_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i):=holomorphic i
lemma inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm :=
  ComplexCurveHomeomorphInverse318.inverse (comparison i) (forward_holomorphic i)
lemma actual_scheme (p:CharacterBase i) :
    LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i) (comparison i p)=
      NormalizedLegendreFieldPoints318.schemeEquiv (branchParameter i) (completedMap i p) :=
  PELOriginalCompletedIndependentMap318.actual_scheme i p
lemma actual_projection (p:CharacterBase i) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i) (comparison i p))=
      PELOriginalCommonLegendreBase318.originalProjection i p :=
  PELOriginalCompletedIndependentMap318.actual_projection i p
end PELOriginalCompletedBiholomorph318
