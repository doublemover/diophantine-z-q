module
public import AffineQuotientPullback318
public section
noncomputable section
namespace QuotientOpenRange318
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) (J : Ideal B)
  (hJ : J = Ideal.map f.hom I) [IsOpenImmersion (Spec.map f)]
lemma range : (Spec.map (AffineQuotientPullback318.arrow f I J hJ)).opensRange =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ (Spec.map f).opensRange := by
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange] using
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (AffineQuotientPullback318.pullback_square f I J hJ) ⊤
end QuotientOpenRange318
