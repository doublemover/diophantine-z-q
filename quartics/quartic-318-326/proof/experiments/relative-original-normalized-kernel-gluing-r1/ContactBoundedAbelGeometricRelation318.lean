module
public import ContactPicardGeometricCoverCriterion318
public section
noncomputable section
namespace ContactBoundedAbelGeometricRelation318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
/-- The original all-bound Cartier-difference Abel fiber relation is the
actual geometric image sieve. This retains O(D-E), not only divisor support
or degree and not a substitute elliptic or generic-fiber relation. -/
lemma sieve_eq_image :
    ContactDifferenceAbsoluteRelation318.sieve c B D E=
      MorphismImageSieve318.image (ContactRelationProjectionImage318.projection R c L K) :=
  ContactRelationProjectionImage318.equalizer_eq_image R c L K
lemma abel_iff_generated_covering :
    (ContactCartierDifferenceAbel318.transformation c).app (op B) D=
      (ContactCartierDifferenceAbel318.transformation c).app (op B) E ↔
    Sieve.ofArrows (fun _ : PUnit => ContactRelationProjectionImage318.object R c L K)
      (fun _ => ContactRelationProjectionImage318.projection R c L K) ∈
        RelativeFppfLineSheaf318.topology Q B := by
  rw [ContactDifferenceAbsoluteRelation318.abel_iff_covering,
    sieve_eq_image,MorphismImageSieve318.generated]
/-- The actual bounded Abel relation commutes with every whole-site
base change via a literal categorical pullback of its geometric witness. -/
lemma pullback_sieve (T : Over Q) (f : T ⟶ B) :
    (ContactDifferenceAbsoluteRelation318.sieve c B D E).pullback f=
      MorphismImageSieve318.image
        (ContactRelationImageBaseChange318.projection R c L K T f) := by
  rw [sieve_eq_image,MorphismImageSieve318.pullback_image]
end ContactBoundedAbelGeometricRelation318
