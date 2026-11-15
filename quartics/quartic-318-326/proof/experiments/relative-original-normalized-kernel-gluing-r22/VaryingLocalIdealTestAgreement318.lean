module
public import VaryingLocalFreeIdealCover318
public section
noncomputable section
namespace VaryingLocalIdealTestAgreement318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open VaryingLocalFreeIdealCover318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : Ideal (S ⊗[R] A)) (C : Data R A ι S I)
variable (i j : C.coefficients.Index) (T : Type u) [CommRing T] [Algebra R T]
  (f : C.coefficients.ring i →ₐ[R] T) (g : C.coefficients.ring j →ₐ[R] T)
  (h : f.comp (C.coefficients.coefficient i)=g.comp (C.coefficients.coefficient j))
/-- The original full ideal makes local classifying maps agree on EVERY
actual common affine coefficient test. Whole ideal extension, not frame
matching or pointwise support, supplies the equality. -/
lemma agreement : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ localMap R A ι S I C i=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ localMap R A ι S I C j := by
  rw [localMap,localMap,VaryingFreeIdealClassifyingMap318.natural,
    VaryingFreeIdealClassifyingMap318.natural]
  apply congrArg (VaryingFreeIdealClassifyingMap318.classify R A ι T)
  apply Subtype.ext
  rw [VaryingFreeIdealClassifyingMap318.mapIdeal_val,VaryingFreeIdealClassifyingMap318.mapIdeal_val]
  change Ideal.map _ (Ideal.map _ I)=Ideal.map _ (Ideal.map _ I)
  rw [VaryingSourceMapComposition318.ideal_map,VaryingSourceMapComposition318.ideal_map,h]
end VaryingLocalIdealTestAgreement318
