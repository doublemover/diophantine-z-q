module
public import ContactAbelDiagonalCover318
public section
noncomputable section
namespace ContactOriginalPicardDiagonalImage318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "v" => ContactCartierDifferenceAbel318.transformation c
local notation "F" => (ContactDifferenceSheafEpimorphism318.target c).obj
variable (D E : A.obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "π" => ContactRelationProjectionImage318.projection R c L K
/-- The literal whole-site fiber of the original Picard diagonal at
these two actual all-bound Cartier-difference families. -/
@[expose] def kernel := WholePresheafDiagonalFiber318.presheaf F (v.app (op B) D) (v.app (op B) E)
@[expose] def relationMap : yoneda.obj (ContactRelationProjectionImage318.object R c L K) ⟶
    kernel R c D E :=
  WholeGeometricDiagonalImage318.lift F (v.app (op B) D) (v.app (op B) E) π
    (ContactAbelUniversalIsomInvariant318.invariant c R inferInstance D E)
lemma projection : relationMap R c D E ≫
    WholePresheafDiagonalFiber318.inclusion F (v.app (op B) D) (v.app (op B) E)=yoneda.map π := rfl
lemma image_sieve (T : Over Q) (f : (kernel R c D E).obj (op T)) :
    Presheaf.imageSieve (relationMap R c D E) f=(MorphismImageSieve318.image π).pullback f.val :=
  WholeGeometricDiagonalImage318.image_sieve F _ _ π _ T f
/-- Produced local surjectivity on the actual diagonal fiber, NOT an
isomorphism: distinct full line isomorphisms may have the same base point. -/
instance locallySurjective : Presheaf.IsLocallySurjective J (relationMap R c D E) :=
  WholeGeometricDiagonalImage318.locallySurjective F _ _ π _ J
    (fun T f => ContactAbelDiagonalCover318.covering R c D E T f.val f.property)
lemma local_range_eq_top :
    (Subfunctor.range (relationMap R c D E)).sheafify J=⊤ :=
  (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J (relationMap R c D E)).mp inferInstance
end ContactOriginalPicardDiagonalImage318
