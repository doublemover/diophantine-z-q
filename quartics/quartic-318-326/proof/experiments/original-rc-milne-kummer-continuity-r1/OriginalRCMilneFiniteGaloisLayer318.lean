module
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.FieldTheory.AbsoluteGaloisGroup

public section
noncomputable section

namespace OriginalRCMilneFiniteGaloisLayer318

variable {F : Type*} [Field F] [CharZero F]
local notation "Fb" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local notation "GalAlg" => (Fb ≃ₐ[F] Fb)

abbrev asAlg (g : Gal) : GalAlg := g

/-- The literal finite normal hull of the supplied coordinate set inside
the very same algebraic closure; no moved field or unknown cover. -/
def layer (S : Finset Fb) : FiniteGaloisIntermediateField F Fb :=
  FiniteGaloisIntermediateField.adjoin F (S : Set Fb)

theorem layer_mem (S : Finset Fb) {x : Fb} (hx : x ∈ S) :
    x ∈ (layer S).toIntermediateField :=
  FiniteGaloisIntermediateField.subset_adjoin F (S : Set Fb) hx

abbrev Auto (S : Finset Fb) :=
  (layer S).toIntermediateField ≃ₐ[F] (layer S).toIntermediateField

/-- Literal restriction from the actual absolute Galois group. -/
def restriction (S : Finset Fb) : Gal →* Auto S :=
  show GalAlg →* Auto S from AlgEquiv.restrictNormalHom (layer S).toIntermediateField

theorem fixing_iff (S : Finset Fb) (g : Gal) :
    restriction S g=1 ↔ asAlg g ∈ (layer S).toIntermediateField.fixingSubgroup := by
  change asAlg g ∈ (AlgEquiv.restrictNormalHom (layer S).toIntermediateField).ker ↔ _
  rw [(layer S).toIntermediateField.restrictNormalHom_ker]

theorem restriction_surjective (S : Finset Fb) : Function.Surjective (restriction S) :=
  AlgEquiv.restrictNormalHom_surjective (K₁ := (layer S).toIntermediateField) Fb

theorem restriction_same_coordinate (S : Finset Fb) (g h : Gal)
    (he : restriction S g=restriction S h) {x : Fb} (hx : x∈S) :
    asAlg g x=asAlg h x := by
  let X : (layer S).toIntermediateField := ⟨x,layer_mem S hx⟩
  have hv := congrArg (fun σ : Auto S => (σ X).val) he
  simpa only [restriction,AlgEquiv.restrictNormalHom_apply] using hv

/-- Choose a lift only to define the scalar on this finite argument
group. No half-point or Kummer representative is reselected. -/
def factor (S : Finset Fb) {Y : Type*} (z : Gal → Y) : Auto S → Y :=
  fun a => z (Classical.choose (restriction_surjective S a))

theorem factor_eval (S : Finset Fb) {Y : Type*} (z : Gal → Y)
    (hf : ∀ g h : Gal, restriction S g=restriction S h → z g=z h) (g : Gal) :
    factor S z (restriction S g)=z g :=
  hf _ g (Classical.choose_spec (restriction_surjective S (restriction S g)))

/-- The finite restriction's fibres are open via its actual fixing
subgroup and left translation in the actual Krull topology. -/
theorem locallyConstant_of_fibres (S : Finset Fb) {Y : Type*} (z : Gal → Y)
    (hf : ∀ g h : Gal, restriction S g=restriction S h → z g=z h) :
    IsLocallyConstant z := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  let H : Set Gal := fun h => asAlg h ∈ (layer S).toIntermediateField.fixingSubgroup
  have hOpen : IsOpen H := by
    change IsOpen ((layer S).toIntermediateField.fixingSubgroup : Set GalAlg)
    exact (layer S).toIntermediateField.fixingSubgroup_isOpen
  refine ⟨(fun h : Gal => g⁻¹*h) ⁻¹' H,hOpen.preimage (continuous_const.mul continuous_id),?_,?_⟩
  · change asAlg (g⁻¹*g) ∈ (layer S).toIntermediateField.fixingSubgroup
    rw [inv_mul_cancel]
    exact (layer S).toIntermediateField.fixingSubgroup.one_mem
  · intro h hh
    have hfix : restriction S (g⁻¹*h)=1 :=
      (fixing_iff S _).mpr hh
    rw [map_mul,map_inv] at hfix
    apply hf h g
    have ha := congrArg (fun z : Auto S => restriction S g*z) hfix
    simpa only [←mul_assoc,mul_inv_cancel,one_mul,mul_one] using ha

end OriginalRCMilneFiniteGaloisLayer318

#print axioms OriginalRCMilneFiniteGaloisLayer318.restriction_same_coordinate
#print axioms OriginalRCMilneFiniteGaloisLayer318.locallyConstant_of_fibres
