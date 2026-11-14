module
public import ContactPicardDiagonalSheafImage318
public section
noncomputable section
namespace ContactPicardDiagonalImageFactorization318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "B" => Over.mk (baseMap R)
local notation "F" => (ContactDifferenceSheafEpimorphism318.target c).obj
local notation "v" => ContactCartierDifferenceAbel318.transformation c
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "π" => ContactRelationProjectionImage318.projection R c L K
local notation "Y" => yoneda.obj (ContactRelationProjectionImage318.object R c L K)
local notation "V" => ContactOriginalPicardDiagonalImage318.kernel R c D E
local notation "ι" => WholePresheafDiagonalFiber318.inclusion F (v.app (op B) D) (v.app (op B) E)
@[expose] def baseSheaf : Sheaf J (Type 1) := (presheafToSheaf J (Type 1)).obj (yoneda.obj B)
instance inclusionLocallyInjective : Presheaf.IsLocallyInjective J ι :=
  Presheaf.isLocallyInjective_of_injective J ι
    (fun T => WholePresheafDiagonalFiber318.inclusion_injective F _ _ T.unop)
@[expose] def inclusionTransformation : V ⟶ (baseSheaf R).obj := ι ≫ toSheafify J (yoneda.obj B)
instance inclusionTransformationLocallyInjective :
    Presheaf.IsLocallyInjective J (inclusionTransformation R c D E) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (ι ≫ toSheafify J (yoneda.obj B)))
/-- The associated actual diagonal fiber is a SUBOBJECT of the
associated original base, not a scheme asserted to represent that subobject. -/
@[expose] def inclusion : ContactPicardDiagonalSheafImage318.target R c D E ⟶ baseSheaf R :=
  ⟨sheafifyLift J (inclusionTransformation R c D E) (baseSheaf R).property⟩
lemma unit_inclusion : toSheafify J V ≫ (inclusion R c D E).hom=inclusionTransformation R c D E :=
  toSheafify_sheafifyLift J (inclusionTransformation R c D E) (baseSheaf R).property
instance locallyInjective : Sheaf.IsLocallyInjective (inclusion R c D E) :=
  Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
    (inclusionTransformation R c D E) (unit_inclusion R c D E)
instance mono : Mono (inclusion R c D E) := Sheaf.mono_of_isLocallyInjective (inclusion R c D E)
@[expose] def projection : ContactPicardDiagonalSheafImage318.source R c D E ⟶ baseSheaf R :=
  ⟨sheafifyLift J (yoneda.map π ≫ toSheafify J (yoneda.obj B)) (baseSheaf R).property⟩
lemma unit_projection : toSheafify J Y ≫ (projection R c D E).hom=
    yoneda.map π ≫ toSheafify J (yoneda.obj B) :=
  toSheafify_sheafifyLift J (yoneda.map π ≫ toSheafify J (yoneda.obj B)) (baseSheaf R).property
/-- An ACTUAL epi-mono factorization of the original geometric relation
projection after sheafification. The epi loses automorphism data; it is
not claimed injective or an isomorphism of represented schemes. -/
lemma factor : ContactPicardDiagonalSheafImage318.map R c D E ≫ inclusion R c D E=
    projection R c D E := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (baseSheaf R).property
  change toSheafify J Y ≫ ((ContactPicardDiagonalSheafImage318.map R c D E).hom ≫
    (inclusion R c D E).hom)=toSheafify J Y ≫ (projection R c D E).hom
  rw [←Category.assoc,ContactPicardDiagonalSheafImage318.unit_map,unit_projection]
  change (ContactOriginalPicardDiagonalImage318.relationMap R c D E ≫ toSheafify J V) ≫
    (inclusion R c D E).hom=_
  rw [Category.assoc,unit_inclusion]
  change ContactOriginalPicardDiagonalImage318.relationMap R c D E ≫
    (ι ≫ toSheafify J (yoneda.obj B))=_
  rw [←Category.assoc,ContactOriginalPicardDiagonalImage318.projection]
end ContactPicardDiagonalImageFactorization318
