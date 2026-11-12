module
public import AffineSpecOriginalRingTransport318
public section
noncomputable section
namespace AffineSpecOriginalRingEquivalence318
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : CommRingCat.{u}} (e : Spec B ≅ Spec A)

lemma inverse (b : B) : AffineSpecOriginalRingTransport318.hom e
    (AffineSpecOriginalRingTransport318.hom e.symm b) = b := by
  have h : Spec.preimage e.inv ≫ Spec.preimage e.hom = 𝟙 B := by
    apply Spec.map_injective
    simpa only [Spec.map_comp,Spec.map_preimage,Spec.map_id] using e.hom_inv_id
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) b

/-- The actual full original affine scheme isomorphism, reflected as a
ring isomorphism in the correct contravariant direction. -/
@[expose] def equivalence : A ≃+* B where
  __ := AffineSpecOriginalRingTransport318.hom e
  invFun := AffineSpecOriginalRingTransport318.hom e.symm
  left_inv := inverse e.symm
  right_inv := inverse e
end AffineSpecOriginalRingEquivalence318
