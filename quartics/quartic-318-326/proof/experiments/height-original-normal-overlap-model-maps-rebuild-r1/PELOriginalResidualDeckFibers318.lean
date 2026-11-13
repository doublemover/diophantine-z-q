module
public import PELOriginalResidualDeckAction318
public section
noncomputable section
namespace PELOriginalResidualDeckFibers318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalInvolutionTower318 PELOriginalInvolutionFiber318
open PELOriginalResidualDeckAction318
set_option maxHeartbeats 1800000

instance (i : Fin 4) : Finite (Deck i) :=
  Finite.of_surjective (deckMap i) (deckMap_surjective i)

@[expose] def orbitFiber (i : Fin 4) (y : InvolutionBase i) (g : Deck i) :
    {z : InvolutionBase i // toCharacterBase i z=toCharacterBase i y} :=
  ⟨g • y,deck_over_base i g y⟩

theorem orbitFiber_bijective (i : Fin 4) (y : InvolutionBase i) :
    Function.Bijective (orbitFiber i y) := by
  constructor
  · intro g h he
    have hv : g • y=h • y := congrArg Subtype.val he
    have hf : (h⁻¹*g) • y=y := by rw [mul_smul,hv,inv_smul_smul]
    have hh := (deck_fixed_iff i (h⁻¹*g) y).mp hf
    have ht := congrArg (fun k : Deck i => h*k) hh
    simpa only [mul_inv_cancel_left,mul_one] using ht
  · rintro ⟨z,hz⟩
    obtain ⟨g,hg⟩ := (fiber_iff_orbit i z y).mp hz
    exact ⟨g,Subtype.ext hg⟩

/-- A fiber is a torsor for the actual residual group: this is an explicit
bijection for EVERY base point, not an equality of finite cardinalities. -/
@[expose] def fiberEquiv (i : Fin 4) (y : InvolutionBase i) :
    Deck i ≃ {z : InvolutionBase i // toCharacterBase i z=toCharacterBase i y} :=
  Equiv.ofBijective (orbitFiber i y) (orbitFiber_bijective i y)

theorem deck_card (i : Fin 4) : Nat.card (Deck i)=4 := by
  let y := toInvolution i (PELOriginalLabeledFixedOrbits318.originalPoint 0)
  exact (Nat.card_congr (fiberEquiv i y)).trans (every_fiber_four i (toCharacterBase i y))

theorem labels_square (v : Labels) : v*v=1 := by
  revert v
  decide

/-- The residual four-group has exponent TWO. This rules out replacing
this original cover by an arbitrary degree-four cyclic cover. -/
theorem deck_square (i : Fin 4) (g : Deck i) : g*g=1 := by
  obtain ⟨k,rfl⟩ := deckMap_surjective i g
  have hk : k*k=1 := Subtype.ext (labels_square (k:Labels))
  rw [←map_mul,hk,map_one]

theorem deck_commute (i : Fin 4) (g h : Deck i) : g*h=h*g := by
  obtain ⟨k,rfl⟩ := deckMap_surjective i g
  obtain ⟨l,rfl⟩ := deckMap_surjective i h
  rw [←map_mul,←map_mul,mul_comm k l]

/-- Each nonidentity residual automorphism is an involution with NO fixed
point on the actual source curve. Elliptic group laws are not assumed. -/
theorem nontrivial_deck_involution (i : Fin 4) (g : Deck i) (hg : g≠1) :
    g*g=1 ∧ ∀ y : InvolutionBase i,g • y≠y :=
  ⟨deck_square i g,fun y h => hg ((deck_fixed_iff i g y).mp h)⟩
end PELOriginalResidualDeckFibers318
