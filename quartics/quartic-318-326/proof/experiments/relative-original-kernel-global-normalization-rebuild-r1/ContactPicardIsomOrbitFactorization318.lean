module
public import ContactPicardIsomOrbitSheaf318
public section
noncomputable section
namespace ContactPicardIsomOrbitFactorization318
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
local notation "O" => ContactPicardIsomOrbitPresheaf318.presheaf R c D E
@[expose] def transformation : Y ⟶ (ContactPicardIsomOrbitSheaf318.sheaf R c D E).obj :=
  ContactPicardIsomOrbitPresheaf318.quotient R c D E ≫ toSheafify J O
@[expose] def map : ContactPicardDiagonalSheafImage318.source R c D E ⟶
    ContactPicardIsomOrbitSheaf318.sheaf R c D E :=
  ⟨sheafifyLift J (transformation R c D E) (ContactPicardIsomOrbitSheaf318.sheaf R c D E).property⟩
lemma unit_map : toSheafify J Y ≫ (map R c D E).hom=transformation R c D E :=
  toSheafify_sheafifyLift J _ _
/-- The old original Isom-to-diagonal map factors through the ACTUAL
full-stabilizer orbit quotient, with exactly the old target and map. -/
lemma factor : map R c D E ≫ ContactPicardIsomOrbitSheaf318.map R c D E=
    ContactPicardDiagonalSheafImage318.map R c D E := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (ContactPicardDiagonalSheafImage318.target R c D E).property
  change toSheafify J Y ≫ ((map R c D E).hom ≫
    (ContactPicardIsomOrbitSheaf318.map R c D E).hom)=_
  rw [←Category.assoc,unit_map,ContactPicardDiagonalSheafImage318.unit_map]
  change (ContactPicardIsomOrbitPresheaf318.quotient R c D E ≫ toSheafify J O) ≫ _=_
  rw [Category.assoc,ContactPicardIsomOrbitSheaf318.unit_map]
  change ContactPicardIsomOrbitPresheaf318.quotient R c D E ≫
    (ContactPicardIsomOrbitPresheaf318.inclusion R c D E ≫ _) = _
  rw [←Category.assoc,ContactPicardIsomOrbitPresheaf318.factor]
instance epi : Epi (map R c D E) := epi_of_epi_fac (factor R c D E)
lemma base_factor : map R c D E ≫ ContactPicardIsomOrbitSheaf318.map R c D E ≫
    ContactPicardDiagonalImageFactorization318.inclusion R c D E=
      ContactPicardDiagonalImageFactorization318.projection R c D E := by
  rw [←Category.assoc,factor,ContactPicardDiagonalImageFactorization318.factor]
end ContactPicardIsomOrbitFactorization318
