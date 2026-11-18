module
public import ContactOriginalPicardDiagonalImage318
public section
noncomputable section
namespace ContactPicardDiagonalSheafImage318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "B" => Over.mk (baseMap R)
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "Y" => yoneda.obj (ContactRelationProjectionImage318.object R c L K)
local notation "V" => ContactOriginalPicardDiagonalImage318.kernel R c D E
@[expose] def source : Sheaf J (Type 1) := (presheafToSheaf J (Type 1)).obj Y
@[expose] def target : Sheaf J (Type 1) := (presheafToSheaf J (Type 1)).obj V
@[expose] def transformation : Y ⟶ (target R c D E).obj :=
  ContactOriginalPicardDiagonalImage318.relationMap R c D E ≫ toSheafify J V
instance transformationLocallySurjective : Presheaf.IsLocallySurjective J (transformation R c D E) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (ContactOriginalPicardDiagonalImage318.relationMap R c D E ≫ toSheafify J V))
/-- The associated sheaf of the ACTUAL represented Isom parameter maps
epimorphically onto the associated sheaf of the actual diagonal fiber.
No subcanonical theorem or scheme representation of that image is assumed. -/
@[expose] def map : source R c D E ⟶ target R c D E :=
  ⟨sheafifyLift J (transformation R c D E) (target R c D E).property⟩
lemma unit_map : toSheafify J Y ≫ (map R c D E).hom=transformation R c D E :=
  toSheafify_sheafifyLift J (transformation R c D E) (target R c D E).property
instance locallySurjective : Sheaf.IsLocallySurjective (map R c D E) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (unit_map R c D E)
instance epi : Epi (map R c D E) := Sheaf.epi_of_isLocallySurjective' (map R c D E)
end ContactPicardDiagonalSheafImage318
