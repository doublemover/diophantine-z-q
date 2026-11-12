module
public import ContactProjectivePresentationPullbackMaps318
public section
noncomputable section
namespace ContactProjectivePresentationPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveLocalPresentation318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) {Z W : Scheme.{0}}
  (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c)
  (r : W ⟶ ContactRelativeLinearOpenChart318.curve T c) [IsClosedImmersion q] [IsClosedImmersion r]
  (h : W ⟶ Z)
  (H : IsPullback h r q (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
    (ContactIntrinsicDifferentials318.structureMap c))) (D : Data c n S q)
/-- Arbitrary coefficient base change produces a genuine local
presentation over the whole affine refinement of the pulled-back cover. -/
@[expose] def data : Data c n T r where
  coefficients := AffineCoefficientPullbackTests318.data ℚ S T φ D.coefficients
  chart i := D.chart i.1
  ideal := ContactProjectivePresentationPullbackMaps318.ideal c n S T φ q D
  toFamily := ContactProjectivePresentationPullbackMaps318.toFamily c n S T φ q r h H D
  cartesian := ContactProjectivePresentationPullbackMaps318.cartesian c n S T φ q r h H D
end ContactProjectivePresentationPullback318
