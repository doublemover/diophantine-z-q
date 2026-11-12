module
public import ContactDifferenceQuotientComparison318
public section
noncomputable section
namespace ContactDifferenceQuotientSheaf318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
local notation "J" => RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ))
local notation "Q" => ContactDifferenceQuotientPresheaf318.presheaf c
local notation "T" => ContactDifferenceSheafEpimorphism318.target c
@[expose] def source : Sheaf J (Type 1) := (presheafToSheaf J (Type 1)).obj Q
@[expose] def map : source c ⟶ T :=
  ⟨sheafifyLift J (ContactDifferenceQuotientComparison318.transformation c) T.property⟩
lemma unit_map : toSheafify J Q ≫ (map c).hom=ContactDifferenceQuotientComparison318.transformation c :=
  toSheafify_sheafifyLift J (ContactDifferenceQuotientComparison318.transformation c) T.property
instance locallySurjective : Sheaf.IsLocallySurjective (map c) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (unit_map c)
instance locallyInjective : Sheaf.IsLocallyInjective (map c) :=
  Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
    (ContactDifferenceQuotientComparison318.transformation c) (unit_map c)
instance mono : Mono (map c) := Sheaf.mono_of_isLocallyInjective (map c)
instance epi : Epi (map c) := Sheaf.epi_of_isLocallySurjective' (map c)
/-- The original relative fppf Picard sheaf is the associated sheaf of
the explicit actual bounded-divisor-difference quotient by local whole
base-line isomorphisms. This is an isomorphism of SHEAVES, not a scheme
representability or original Jacobian identification theorem. -/
instance isIso : IsIso (map c) := isIso_of_mono_of_epi (map c)
@[expose] def equivalence : source c ≅ T := asIso (map c)
end ContactDifferenceQuotientSheaf318
