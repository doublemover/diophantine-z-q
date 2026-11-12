module
public import PELOriginalInvolutionVisibleLocus318
public import PELOriginalCharacterProjection318
public section
noncomputable section
namespace PELOriginalInvolutionVisibleSquare318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318
open PELOriginalCharacterQuotient318 PELOriginalCharacterLocalSquare318
open PELOriginalInvolutionTower318 PELOriginalInvolutionComplexAtlas318
open PELOriginalInvolutionLocalCover318 PELOriginalInvolutionMaximalFibers318
open PELOriginalCharacterBranches318 (CharacterBranchValues)
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
open PELOriginalMaximalQuotient318
open scoped Manifold ContDiff
set_option maxHeartbeats 2400000
variable (i : Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i) :=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i
local instance : ChartedSpace ℂ MaximalBase := PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := PELMaximalComplexAtlas318.maximal_manifold

/-- The degree-eight map is the original holomorphic composition, not an
independently chosen map with the right finite degree. -/
theorem toOriginalMaximal_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toOriginalMaximal i) :=
  (PELOriginalCharacterProjection318.toMaximal_holomorphic i).comp
    (toCharacterBase_holomorphic i)

theorem lifted_visible_square (j : Fin 5) (τ : HalfPlane)
    (hj : PELUnlevelledComplexBase318.projection τ∈fixedLocus j)
    (hv : InertiaLabels318.fiveLabels j i≠0) :
    ∃ (e : OpenPartialHomeomorph (InvolutionBase i) ℂ)
      (b : OpenPartialHomeomorph MaximalBase ℂ),
      toInvolution i (PELUnlevelledComplexBase318.projection τ)∈e.source ∧
      e (toInvolution i (PELUnlevelledComplexBase318.projection τ))=0 ∧
      PELMaximalTopologicalAtlas318.OriginalChart b ∧
      ∀ y∈e.source,toOriginalMaximal i y∈b.source ∧
        b (toOriginalMaximal i y)=(e y)^2 := by
  obtain ⟨U,c,b,hU,hτU,hcs,hb,hc0,hmodel,_⟩ := visible_local_square i j τ hj hv
  let p := toInvolution i (PELUnlevelledComplexBase318.projection τ)
  let s := localSheet i p
  let e := s.trans c
  have hpS := localSheet_center i p
  have hpC : toCharacterBase i p∈c.source := by
    rw [hcs]
    exact ⟨PELUnlevelledComplexBase318.projection τ,hτU,rfl⟩
  have hpE : p∈e.source := by
    refine ⟨hpS,?_⟩
    change s p∈c.source
    rw [localSheet_value i p p hpS]
    exact hpC
  refine ⟨e,b,hpE,?_,hb,?_⟩
  · change c (s p)=0
    rw [localSheet_value i p p hpS]
    exact hc0
  · intro y hy
    have hs := localSheet_value i p y hy.1
    have hc : toCharacterBase i y∈c.source := by rw [←hs]; exact hy.2
    obtain ⟨hm,he⟩ := hmodel (toCharacterBase i y) hc
    refine ⟨hm,?_⟩
    change b (toMaximal i (toCharacterBase i y))=(c (s y))^2
    rw [hs]
    exact he

/-- Every point of the actual sixteen-point visible source locus has
an exact original z² model. The source chart is on the INVOLUTION curve,
not the character curve or the unrelated level-three parameter line. -/
theorem every_visible_square (p : InvolutionBase i)
    (hp : toOriginalMaximal i p∈CharacterBranchValues i) :
    ∃ (e : OpenPartialHomeomorph (InvolutionBase i) ℂ)
      (b : OpenPartialHomeomorph MaximalBase ℂ),
      p∈e.source ∧ e p=0 ∧ PELMaximalTopologicalAtlas318.OriginalChart b ∧
      ∀ y∈e.source,toOriginalMaximal i y∈b.source ∧
        b (toOriginalMaximal i y)=(e y)^2 := by
  obtain ⟨x,rfl⟩ := toInvolution_surjective i p
  obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective x
  obtain ⟨j,hj,hq⟩ := (PELOriginalDirectCharacterBranches318.branch_values_iff i _).mp hp
  have hfix : PELUnlevelledComplexBase318.projection τ∈fixedLocus j :=
    (PELOriginalDirectBranchEnumeration318.original_fixed_locus_one_orbit j _).mpr hq
  exact lifted_visible_square i j τ hfix hj
end PELOriginalInvolutionVisibleSquare318
