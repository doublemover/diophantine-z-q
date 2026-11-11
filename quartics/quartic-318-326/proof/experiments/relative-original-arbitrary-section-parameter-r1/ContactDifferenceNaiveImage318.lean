module
public import ContactDifferenceAffineImage318
public section
noncomputable section
namespace ContactDifferenceNaiveImage318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- EVERY naive relative class on EVERY scheme test has a covering
actual difference-image sieve. The complete actual affine coefficient
cover is used, not a finite-type/reduced or affine-only substitute. -/
lemma covering (B : Over (Spec (CommRingCat.of ℚ)))
    (x : (RelativeLineClassBaseChange318.presheaf p).obj (op B)) :
    Presheaf.imageSieve (ContactCartierDifferenceAbel318.transformation c)
      ((RelativeFppfLineSheaf318.unit p).app (op B) x) ∈
        RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) B := by
  apply LocalImageCoverDescent318.sieve_of_cover _
    (OriginalAffineCoefficientCover318.object B.hom) (OriginalAffineCoefficientCover318.arrow B.hom)
    (OriginalAffineCoefficientCover318.covering B.hom)
  intro i
  rw [Presheaf.pullback_imageSieve]
  have hn := ConcreteCategory.congr_hom ((RelativeFppfLineSheaf318.unit p).naturality
    (OriginalAffineCoefficientCover318.arrow B.hom i).op) x
  change (RelativeFppfLineSheaf318.unit p).app (op (OriginalAffineCoefficientCover318.object B.hom i))
      ((RelativeLineClassBaseChange318.presheaf p).map (OriginalAffineCoefficientCover318.arrow B.hom i).op x)=
    (RelativeFppfLineSheaf318.sheaf p).obj.map (OriginalAffineCoefficientCover318.arrow B.hom i).op
      ((RelativeFppfLineSheaf318.unit p).app (op B) x) at hn
  rw [←hn]
  exact ContactDifferenceAffineImage318.covering c (OriginalAffineCoefficientCover318.ring B.hom i) _
end ContactDifferenceNaiveImage318
