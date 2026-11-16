module
public import ContactPicardIsomOrbitPresheaf318
public section
noncomputable section
namespace ContactPicardIsomOrbitSheaf318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "B" => Over.mk (baseMap R)
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "O" => ContactPicardIsomOrbitPresheaf318.presheaf R c D E
local notation "V" => ContactOriginalPicardDiagonalImage318.kernel R c D E
local notation "ι" => ContactPicardIsomOrbitPresheaf318.inclusion R c D E
@[expose] def sheaf : Sheaf J (Type 1) := (presheafToSheaf J (Type 1)).obj O
instance inclusionLocallyInjective : Presheaf.IsLocallyInjective J ι :=
  WholeMorphismOrbitImage318.locallyInjective _ J
instance inclusionLocallySurjective : Presheaf.IsLocallySurjective J ι :=
  WholeMorphismOrbitImage318.locallySurjective _ J
@[expose] def transformation : O ⟶ (ContactPicardDiagonalSheafImage318.target R c D E).obj :=
  ι ≫ toSheafify J V
instance transformationLocallyInjective : Presheaf.IsLocallyInjective J (transformation R c D E) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (ι ≫ toSheafify J V))
instance transformationLocallySurjective : Presheaf.IsLocallySurjective J (transformation R c D E) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (ι ≫ toSheafify J V))
@[expose] def map : sheaf R c D E ⟶ ContactPicardDiagonalSheafImage318.target R c D E :=
  ⟨sheafifyLift J (transformation R c D E) (ContactPicardDiagonalSheafImage318.target R c D E).property⟩
lemma unit_map : toSheafify J O ≫ (map R c D E).hom=transformation R c D E :=
  toSheafify_sheafifyLift J _ _
instance locallyInjective : Sheaf.IsLocallyInjective (map R c D E) :=
  Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
    (transformation R c D E) (unit_map R c D E)
instance locallySurjective : Sheaf.IsLocallySurjective (map R c D E) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (unit_map R c D E)
instance mono : Mono (map R c D E) := Sheaf.mono_of_isLocallyInjective _
instance epi : Epi (map R c D E) := Sheaf.epi_of_isLocallySurjective' _
instance isIso : IsIso (map R c D E) := isIso_of_mono_of_epi _
/-- The quotient by the FULL stabilizer represents the diagonal image
only as an associated SHEAF. No scheme representing this orbit quotient
or subcanonical identification is assumed or concluded. -/
@[expose] def equivalence : sheaf R c D E ≅ ContactPicardDiagonalSheafImage318.target R c D E :=
  asIso (map R c D E)
end ContactPicardIsomOrbitSheaf318
