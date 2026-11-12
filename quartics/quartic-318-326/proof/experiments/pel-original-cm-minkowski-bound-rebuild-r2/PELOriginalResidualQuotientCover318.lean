module
public import PELOriginalInvolutionRamification318
public import Mathlib.Topology.Covering.Quotient
public section
noncomputable section
namespace PELOriginalResidualQuotientCover318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalCharacterTopology318 PELOriginalInvolutionTower318
open PELOriginalInvolutionLocalCover318 PELOriginalResidualDeckAction318
open PELOriginalResidualDeckFibers318 PELOriginalResidualDeckHolomorphy318
open Topology
set_option maxHeartbeats 2000000

instance residualContinuous (i : Fin 4) : ContinuousConstSMul (Deck i) (InvolutionBase i) where
  continuous_const_smul g := deck_continuous i g

/-- Openness is proved for the ACTUAL map, by its square with the two
original open quotient projections. -/
theorem residual_open (i : Fin 4) : IsOpenMap (toCharacterBase i) := by
  intro U hU
  have he : toCharacterBase i '' U = toCharacter i '' (toInvolution i ⁻¹' U) := by
    ext q
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,rfl⟩ := toInvolution_surjective i y
      exact ⟨x,hy,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨toInvolution i x,hx,rfl⟩
  rw [he]
  exact toCharacter_open i _ (hU.preimage (toInvolution_continuous i))

theorem residual_openQuotient (i : Fin 4) : IsOpenQuotientMap (toCharacterBase i) where
  surjective := toCharacterBase_surjective i
  continuous := toCharacterBase_continuous i
  isOpenMap := residual_open i

/-- A genuine global regular covering, not only unrelated local sheets
or a four-element fiber count. The deck group is the actual image of the
original character kernel acting on the same involution curve. -/
theorem residual_quotient_cover (i : Fin 4) :
    IsQuotientCoveringMap (toCharacterBase i) (Deck i) := by
  apply (residual_openQuotient i).isQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul
  intro y z
  exact fiber_iff_orbit i y z

theorem residual_covering (i : Fin 4) : IsCoveringMap (toCharacterBase i) :=
  (residual_quotient_cover i).isCoveringMap

/-- The exact residual covering and its whole fibers are simultaneously
retained; this is the cover that must later be identified with elliptic
multiplication-by-two, not an arbitrary isogeny of degree four. -/
theorem original_four_cover (i : Fin 4) :
    IsQuotientCoveringMap (toCharacterBase i) (Deck i) ∧
    Nat.card (Deck i)=4 ∧
    ∀ q : CharacterBase i,Nat.card {p : InvolutionBase i // toCharacterBase i p=q}=4 :=
  ⟨residual_quotient_cover i,deck_card i,PELOriginalInvolutionFiber318.every_fiber_four i⟩
end PELOriginalResidualQuotientCover318
