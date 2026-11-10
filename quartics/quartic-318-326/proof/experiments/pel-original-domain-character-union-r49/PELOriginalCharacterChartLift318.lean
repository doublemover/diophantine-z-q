module
public import PELOriginalCharacterTopologicalAtlas318
public section
noncomputable section
namespace PELOriginalCharacterChartLift318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalBranchLabels318
open PELOriginalFiniteRamification318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (i : Fin 4)

theorem projection_action (g : (character i).ker) (p : UnlevelledBase) :
    toCharacter i ((g : PELOriginalMaximalQuotient318.Labels) • p) = toCharacter i p :=
  (toCharacter_eq_iff i _ _).mpr ⟨g,rfl⟩

/-- Extend retained holomorphic lift evidence to EVERY original representative. -/
theorem lift_holomorphic (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (p : UnlevelledBase) (hp : toCharacter i p ∈ e.source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y => e (toCharacter i y)) p := by
  obtain ⟨U,hU,hs,hhol⟩ := he
  rw [hs] at hp
  obtain ⟨x,hx,hqx⟩ := hp
  obtain ⟨g,hg⟩ := (toCharacter_eq_iff i x p).mp hqx
  have hact := PELOriginalElementaryAction318.original_action_holomorphic
    (g : PELOriginalMaximalQuotient318.Labels)
  have hxhol : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (toCharacter i y)) ((g : PELOriginalMaximalQuotient318.Labels) • p) := by
    rw [hg]
    exact hhol x hx
  have h := hxhol.comp p hact.contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [] with y
  exact congrArg e (projection_action i g y).symm

/-- A finite exceptional set suffices for removable-singularity transitions.
It deliberately contains BOTH visible and omitted inertia images. -/
@[expose] def exceptionalImage : Set (CharacterBase i) :=
  toCharacter i '' nontrivialStabilizerLocus

theorem exceptional_iff (p : UnlevelledBase) :
    toCharacter i p ∈ exceptionalImage i ↔ p ∈ nontrivialStabilizerLocus := by
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨g,hg⟩ := (toCharacter_eq_iff i x p).mp he
    rw [← hg] at hx
    exact (PELStabilizerLocusInvariant318.stabilizer_locus_invariant
      (g : PELOriginalMaximalQuotient318.Labels) p).mp hx
  · exact fun hp => ⟨p,hp,rfl⟩

theorem exceptional_finite : (exceptionalImage i).Finite := by
  have he : exceptionalImage i = Set.range (fun x : Ramification => toCharacter i x.val) := by
    ext q
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
  rw [he]
  exact Set.finite_range _

theorem exceptional_neighborhood (q : CharacterBase i) (hq : q ∈ exceptionalImage i) :
    ∃ W : Set (CharacterBase i), IsOpen W ∧ q ∈ W ∧
      ∀ z ∈ W, z ∈ exceptionalImage i ↔ z = q := by
  let W := (exceptionalImage i \ {q})ᶜ
  refine ⟨W,((exceptional_finite i).diff {q}).isClosed.isOpen_compl,?_,?_⟩
  · intro h
    exact h.2 rfl
  · intro z hz
    constructor
    · intro he
      by_contra hne
      exact hz ⟨he,hne⟩
    · rintro rfl
      exact hq
end PELOriginalCharacterChartLift318
