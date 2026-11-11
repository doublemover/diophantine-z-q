module
public import VaryingGlobalClassifierInjective318
public import AffineIdealEqualityIso318
public section
noncomputable section
namespace VaryingFreeIdealFamilyRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S)
local notation "a" => VaryingFreeIdealClassifyingMap318.representative R A ι S I
local notation "F" => toFramed R A ι S a
abbrev family : Scheme := Spec (CommRingCat.of ((S ⊗[R] A) ⧸ I.val))
abbrev projection : family R A ι S I ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S ((S ⊗[R] A) ⧸ I.val)))
abbrev into : family R A ι S I ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.val))
lemma representative_ideal : ideal F.action F.marked=I.val :=
  congrArg Subtype.val (VaryingFreeIdealClassifyingMap318.representative_ideal R A ι S I)
@[expose] def representativeIso : VaryingCyclicFamilyBaseChange318.family R A ι S a ≅ family R A ι S I :=
  AffineIdealEqualityIso318.iso (S ⊗[R] A) _ _ (representative_ideal R A ι S I)
@[expose] def map : family R A ι S I ⟶ VaryingWordFamilyGluing318.scheme R A ι :=
  (representativeIso R A ι S I).inv ≫ VaryingCyclicGlobalFamilyLift318.map R A ι S a
lemma cartesian : IsPullback (map R A ι S I) (projection R A ι S I)
    (VaryingWordGlobalFamilyProjection318.projection R A ι)
    (VaryingFreeIdealClassifyingMap318.classify R A ι S I) := by
  apply (VaryingCyclicGlobalFamilyRecovery318.cartesian R A ι S a).of_iso
    (representativeIso R A ι S I) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [map,Iso.refl_hom,Category.comp_id,← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  · simpa only [Iso.refl_hom,Category.comp_id] using
      (AffineIdealEqualityIso318.hom_projection (S ⊗[R] A) _ _ (representative_ideal R A ι S I) S).symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
/-- The literal original full-ideal quotient, with no chosen frame in its
carrier, is the actual pullback of the global universal family. -/
@[expose] def comparison : family R A ι S I ≅ pullback
    (VaryingWordGlobalFamilyProjection318.projection R A ι)
    (VaryingFreeIdealClassifyingMap318.classify R A ι S I) :=
  (cartesian R A ι S I).isoPullback
@[reassoc] lemma map_original : map R A ι S I ≫ VaryingWordGlobalOriginalMap318.original R A ι=
    into R A ι S I ≫ VaryingSourceCoefficientPullback318.original R A S := by
  rw [map,Category.assoc,VaryingCyclicGlobalFamilyLift318.map_original,← Category.assoc]
  have hi := AffineIdealEqualityIso318.inv_into (S ⊗[R] A) _ _ (representative_ideal R A ι S I)
  exact congrArg (fun k => k ≫ VaryingSourceCoefficientPullback318.original R A S) hi
end VaryingFreeIdealFamilyRecovery318
