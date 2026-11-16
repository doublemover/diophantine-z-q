module
public import PELOriginalCharacterRegularLocalHomeomorph318
public import ComplexCurveHolomorphicDescent318
public section
noncomputable section
namespace PELOriginalOrderedCharacterBiholomorph318
open CategoryTheory Set Filter
open scoped Topology Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalOrderedCharacterContinuity318
open PELOriginalCharacterChartLift318 PELOriginalContactRootFunctions318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane (parameter i)):=
  LegendreCompletedComplexAtlas318.chartedSpace _
local instance : IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane (parameter i)):=
  LegendreCompletedComplexAtlas318.complex_manifold _

lemma outside_exception (q:CharacterBase i) (hq:q∉exceptionalImage i):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) q:=by
  obtain ⟨p,rfl⟩:=PELOriginalCharacterTopology318.toCharacter_surjective i q
  have hp:p∈RegularSource:=by
    by_contra hn
    exact hq ⟨p,PELOriginalCompletedContactPoints318.ramified_of_not_regular p hn,rfl⟩
  exact ComplexCurveHolomorphicDescent318.at_image (toCharacter i) (comparison i) RegularSource
    (PELOriginalCharacterRegularLocalHomeomorph318.local_homeomorph i) p hp
    (PELOriginalCharacterComplexAtlas318.character_projection_holomorphic i p)
    (PELOriginalOrderedRegularHolomorphy318.source_regular i p hp)

/-- ALL omitted/visible inertia images are removed using the independently
proved continuity of this exact map, in the unchanged source/target atlases. -/
theorem holomorphic:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i):=
  ComplexCurveRemovablePoints318.holomorphic_of_finite_exception (comparison i)
    (PELOriginalOrderedCharacterContinuity318.continuous i) (exceptionalImage i)
    (exceptional_finite i) (outside_exception i)
lemma open_map:IsOpenMap (comparison i):=
  ComplexCurveOpenMapping318.isOpenMap (comparison i) (holomorphic i) Set.univ isOpen_univ dense_univ
    (comparison i).injective.injOn
@[expose] def biholomorph:CharacterBase i≃ₜLegendrePlaneOverlap318.CompletedPlane (parameter i):=
  (comparison i).toHomeomorphOfContinuousOpen
    (PELOriginalOrderedCharacterContinuity318.continuous i) (open_map i)
lemma forward_holomorphic:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (biholomorph i):=holomorphic i
lemma inverse_holomorphic:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (biholomorph i).symm:=
  ComplexCurveHomeomorphInverse318.inverse (biholomorph i) (forward_holomorphic i)
lemma actual_source_square (x:UnlevelledBase):
    (LegendreCompletedPointIdentification318.schemeEquivalence (parameter i)
      (biholomorph i (toCharacter i x))).val=
    (PELOriginalContactSchemePoints318.comparison x).val≫
      PELOriginalWholeCharacterMorphisms318.morphism i:=by
  rw [show biholomorph i (toCharacter i x)=comparison i (toCharacter i x) from rfl,scheme_square] <;> rfl
end PELOriginalOrderedCharacterBiholomorph318
