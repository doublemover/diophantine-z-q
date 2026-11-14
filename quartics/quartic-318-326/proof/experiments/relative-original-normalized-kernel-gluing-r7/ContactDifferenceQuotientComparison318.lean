module
public import ContactDifferenceQuotientPresheaf318
public section
noncomputable section
namespace ContactDifferenceQuotientComparison318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "J" => RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ))
local notation "a" => ContactCartierDifferenceAbel318.transformation c
/-- The original Abel map descends through the explicit actual local
base-twist relation; it is not defined by a new abstract target label. -/
@[expose] def transformation : ContactDifferenceQuotientPresheaf318.presheaf c ⟶
    (ContactDifferenceSheafEpimorphism318.target c).obj where
  app T := Quotient.lift (a.app T) (fun D E h =>
    (ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mpr h)
  naturality T U f := by
    funext x
    induction x using Quotient.inductionOn with
    | h D => exact ConcreteCategory.congr_hom (a.naturality f) D
lemma factor : ContactDifferenceQuotientPresheaf318.quotient c ≫ transformation c=a := rfl
lemma injective (T : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ) : Function.Injective ((transformation c).app T) := by
  intro x y
  induction x,y using Quotient.inductionOn₂ with
  | h D E =>
    intro h
    exact Quotient.sound ((ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mp h)
instance locallyInjective : Presheaf.IsLocallyInjective J (transformation c) :=
  Presheaf.isLocallyInjective_of_injective J (transformation c) (injective c)
instance locallySurjective : Presheaf.IsLocallySurjective J (transformation c) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (factor c)
end ContactDifferenceQuotientComparison318
