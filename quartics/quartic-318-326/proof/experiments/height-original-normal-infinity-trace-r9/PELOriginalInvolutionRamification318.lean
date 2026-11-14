module
public import OriginalLocalSquareObstruction318
public section
noncomputable section
namespace PELOriginalInvolutionRamification318
open PELOriginalInvolutionTower318 PELOriginalInvolutionMaximalFibers318
open PELOriginalCharacterBranches318 (CharacterBranchValues)
open PELOriginalInvolutionVisibleLocus318
set_option maxHeartbeats 2000000

/-- Local unramifiedness of the actual original degree-eight map, defined
by an actual open partial homeomorphism agreeing on its entire source. -/
@[expose] def HasLocalSheet (i : Fin 4) (p : InvolutionBase i) : Prop :=
  ∃ e : OpenPartialHomeomorph (InvolutionBase i) PELOriginalMaximalQuotient318.MaximalBase,
    p∈e.source ∧ ∀ y∈e.source,e y=toOriginalMaximal i y

/-- Exact COMPLETE topological ramification criterion for the original
involution quotient map, including the omitted fifth original branch value. -/
theorem local_sheet_iff (i : Fin 4) (p : InvolutionBase i) :
    HasLocalSheet i p ↔ toOriginalMaximal i p∉CharacterBranchValues i := by
  constructor
  · rintro ⟨s,hps,hsv⟩ hp
    obtain ⟨e,b,hpe,he0,_,hmodel⟩ :=
      PELOriginalInvolutionVisibleSquare318.every_visible_square i p hp
    apply OriginalLocalSquareObstruction318.not_injective_neighborhood
      (toOriginalMaximal i) p e b hpe he0 hmodel s.source s.open_source hps
    intro x hx y hy he
    apply s.injOn hx hy
    rw [hsv x hx,hsv y hy]
    exact he
  · exact PELOriginalInvolutionUnramified318.local_cover i p

/-- Actual ramification, not a separately designated set of labels. -/
abbrev Ramification (i : Fin 4) := {p : InvolutionBase i // ¬ HasLocalSheet i p}

@[expose] def ramificationEquiv (i : Fin 4) : Ramification i ≃ VisibleLocus i :=
  { toFun := fun p => ⟨p.val,by
      by_contra hp
      exact p.property ((local_sheet_iff i p.val).mpr hp)⟩
    invFun := fun p => ⟨p.val,fun hp => (local_sheet_iff i p.val).mp hp p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

instance ramificationFinite (i : Fin 4) : Finite (Ramification i) :=
  Finite.of_equiv _ (ramificationEquiv i).symm

/-- The original degree-eight map has exactly SIXTEEN ramification
points, all with the exact local z² model. The target has four branch values.
This is not the degree-four level-three j-map or its degree-six divisor. -/
theorem ramification_card (i : Fin 4) : Nat.card (Ramification i)=16 := by
  rw [Nat.card_congr (ramificationEquiv i)]
  exact visible_locus_card i
end PELOriginalInvolutionRamification318
