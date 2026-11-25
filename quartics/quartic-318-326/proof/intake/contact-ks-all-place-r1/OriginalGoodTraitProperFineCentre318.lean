module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section
noncomputable section

namespace OriginalGoodTraitProperFineCentre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {R E : Type u} [CommRing R] [IsDomain R]
  [Field E] [Algebra R E] [IsFractionRing R E]

def generic : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R E))

/-- This is the literal fraction map of the retained integer trait. -/
instance : IsDominant (generic (R:=R) (E:=E)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap R E))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical).2
  rw [RingHom.ker_eq_bot.mpr (IsFractionRing.injective R E)]
  exact bot_le

variable [ValuationRing R]
variable {Y S : Scheme.{u}} (p : Y ⟶ S) [IsProper p]
variable (η : Spec (CommRingCat.of E) ⟶ Y) (base : Spec (CommRingCat.of R) ⟶ S)
variable (same : η ≫ p=generic ≫ base)

def valuative : ValuativeCommSq p where
  R := R
  K := E
  i₁ := η
  i₂ := base
  commSq := ⟨same⟩

theorem has_lift : (valuative p η base same).commSq.HasLift := by
  have H : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [←UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  exact H.1 (valuative p η base same)

def chosenLift : (valuative p η base same).commSq.LiftStruct :=
  (has_lift p η base same).exists_lift.some

/-- Applies to the actual original Y₃ at p=2, to the actual Y₁₁
at p=3, or to the local ring at a generic special point when first
spreading the exact generic isomorphism. It extends the whole map. -/
def centre : Spec (CommRingCat.of R) ⟶ Y := (chosenLift p η base same).l

theorem centre_over :
    centre p η base same ≫ p=base := (chosenLift p η base same).fac_right

theorem centre_generic :
    generic ≫ centre p η base same=η := (chosenLift p η base same).fac_left

theorem centre_unique (m : Spec (CommRingCat.of R) ⟶ Y)
    (over : m ≫ p=base) (retains : generic ≫ m=η) :
    m=centre p η base same := by
  apply ext_of_isDominant_of_isSeparated p
    (over.trans (centre_over p η base same).symm) generic
  exact retains.trans (centre_generic p η base same).symm

end OriginalGoodTraitProperFineCentre318
