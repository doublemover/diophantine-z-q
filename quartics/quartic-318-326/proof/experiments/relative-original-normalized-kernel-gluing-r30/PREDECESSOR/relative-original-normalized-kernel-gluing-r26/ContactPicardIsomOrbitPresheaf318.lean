module
public import ContactOriginalIsomOrbitRelation318
public section
noncomputable section
namespace ContactPicardIsomOrbitPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "P" => ContactRelationProjectionImage318.object R c L K
local notation "V" => ContactOriginalPicardDiagonalImage318.kernel R c D E
local notation "φ" => ContactOriginalPicardDiagonalImage318.relationMap R c D E
@[expose] def presheaf := WholeMorphismOrbitPresheaf318.presheaf φ
@[expose] def quotient : yoneda.obj P ⟶ presheaf R c D E := WholeMorphismOrbitPresheaf318.quotient φ
@[expose] def inclusion : presheaf R c D E ⟶ V := WholeMorphismOrbitPresheaf318.inclusion φ
lemma factor : quotient R c D E ≫ inclusion R c D E=φ := rfl
lemma relation_eq_iff (T : Over Q) (z w : T ⟶ P) :
    φ.app (op T) z=φ.app (op T) w ↔ ContactOriginalIsomOrbitRelation318.Related R c L K T z w := by
  rw [ContactOriginalIsomOrbitRelation318.iff_projection]
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
/-- The relation used in the ACTUAL quotient is exactly the produced
full-automorphism orbit relation, not merely an arbitrary fiber relation. -/
lemma quotient_eq_iff_orbit (T : Over Q) (z w : T ⟶ P) :
    (quotient R c D E).app (op T) z=(quotient R c D E).app (op T) w ↔
      ContactOriginalIsomOrbitRelation318.Related R c L K T z w :=
  (WholeMorphismOrbitPresheaf318.quotient_eq_iff φ (op T) z w).trans (relation_eq_iff R c D E T z w)
lemma image_sieve (T : Over Q) (x : V.obj (op T)) :
    Presheaf.imageSieve (inclusion R c D E) x=
      (MorphismImageSieve318.image (ContactRelationProjectionImage318.projection R c L K)).pullback x.val := by
  rw [inclusion,WholeMorphismOrbitImage318.image_sieve,ContactOriginalPicardDiagonalImage318.image_sieve]
end ContactPicardIsomOrbitPresheaf318
