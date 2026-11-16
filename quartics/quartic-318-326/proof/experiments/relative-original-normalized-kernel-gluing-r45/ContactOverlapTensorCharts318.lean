module
public import ContactOriginalLineOverlap318
public import Mathlib.AlgebraicGeometry.Pullbacks

public section
noncomputable section
namespace ContactOverlapTensorCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactOriginalLaurentOverlap318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section PackedTensor
variable (R A B : CommRingCat.{0}) (f : R →+* A) [Algebra R B]
/-- Package the reciprocal tensor and its ring structure together at
ABSTRACT rings, before specializing polynomial/Laurent multiplication. -/
@[expose] def tensorRing : CommRingCat :=
  letI := f.toAlgebra
  CommRingCat.of (A ⊗[R] B)
@[expose] instance tensorLeft : Algebra A (tensorRing R A B f) := by
  letI := f.toAlgebra
  exact Algebra.TensorProduct.leftAlgebra (R:=R) (S:=A) (A:=A) (B:=B)
@[expose] def tensorRight : B →+* tensorRing R A B f :=
  letI := f.toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom
@[expose] def tensorSpecIso :
    pullback (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) ≅ Spec (tensorRing R A B f) := by
  letI := f.toAlgebra
  exact pullbackSpecIso R A B
@[reassoc] lemma tensorSpecIso_inv_base : (tensorSpecIso R A B f).inv ≫
    pullback.fst _ _=Spec.map (CommRingCat.ofHom (algebraMap A (tensorRing R A B f))) := by
  letI := f.toAlgebra
  exact pullbackSpecIso_inv_fst' R A B
@[reassoc] lemma tensorSpecIso_inv_chart : (tensorSpecIso R A B f).inv ≫
    pullback.snd _ _=Spec.map (CommRingCat.ofHom (tensorRight R A B f)) := by
  letI := f.toAlgebra
  exact pullbackSpecIso_inv_snd R A B
end PackedTensor

variable (c : Fin 4 → ℚˣ)

/-- Pasting cancellation proves the actual whole finite chart square over
the literal Laurent localization; it is not a supplied Cartesian premise. -/
lemma finite_cartesian : IsPullback (projection c) (finiteEdge c)
    OriginalLaurentProjectiveOverlap318.finiteInclusion (ContactBicanonicalDegree318.affineMap c) :=
  IsPullback.of_bot' (IsPullback.of_hasPullback
    (ContactProjectiveModel318.modelMap c) OriginalLaurentProjectiveOverlap318.embedding).flip
    (finite_pullback c)

/-- The same cancellation retains the actual reciprocal Laurent map. -/
lemma infinity_cartesian : IsPullback (projection c) (infinityEdge c)
    OriginalLaurentProjectiveOverlap318.infinityInclusion (ContactWholeInfinityScheme318.projection c) := by
  have h := (IsPullback.of_hasPullback (ContactProjectiveModel318.modelMap c)
    OriginalLaurentProjectiveOverlap318.embedding).flip
  change IsPullback (projection c) (into c)
    (OriginalLaurentProjectiveOverlap318.finiteInclusion ≫ JLineAtlas318.chart ℚ 1)
    (ContactProjectiveModel318.modelMap c) at h
  rw [OriginalLaurentProjectiveOverlap318.maps_agree] at h
  exact IsPullback.of_bot' h (ContactWholeInfinityScheme318.original_pullback c)

abbrev finiteRing := OriginalLaurentProjectiveOverlap318.Ring ⊗[Polynomial ℚ]
  ContactKummerOrder318.SourceOrder c

/-- The entire original overlap is the actual tensor spectrum of the whole
finite chart and the original Laurent localization. -/
@[expose] def finiteIso : scheme c ≅ Spec (CommRingCat.of (finiteRing c)) :=
  (finite_cartesian c).isoPullback ≪≫ pullbackSpecIso (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactKummerOrder318.SourceOrder c)

@[reassoc] lemma finiteIso_inv_base : (finiteIso c).inv ≫ projection c =
    Spec.map (CommRingCat.ofHom (algebraMap OriginalLaurentProjectiveOverlap318.Ring (finiteRing c))) := by
  rw [finiteIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactKummerOrder318.SourceOrder c)

@[reassoc] lemma finiteIso_inv_chart : (finiteIso c).inv ≫ finiteEdge c =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R:=Polynomial ℚ) (A:=OriginalLaurentProjectiveOverlap318.Ring)
      (B:=ContactKummerOrder318.SourceOrder c)).toRingHom) := by
  rw [finiteIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactKummerOrder318.SourceOrder c)

/-- The reciprocal tensor uses u↦T⁻¹, not the finite-chart action u↦T.
Its carrier AND ring structure come from the same generic packed tensor. -/
abbrev infinityPacked := tensorRing (CommRingCat.of (Polynomial ℚ))
  (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
  (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom
abbrev infinityRing := (infinityPacked c : Type)
instance infinityRing_commRing : CommRing (infinityRing c) :=
  inferInstanceAs (CommRing (infinityPacked c))
instance infinityRing_laurentAlgebra :
    Algebra OriginalLaurentProjectiveOverlap318.Ring (infinityRing c) :=
  tensorLeft (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom
/-- The SAME canonical right tensor inclusion, typed through its actual
packed reciprocal target instead of reconstructing that target's instances. -/
@[expose] def infinityRight : ContactWholeInfinityAlgebra318.Ring c →+* infinityRing c :=
  tensorRight (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom

@[expose] def infinityIso : scheme c ≅ Spec (CommRingCat.of (infinityRing c)) :=
  (infinity_cartesian c).isoPullback ≪≫ tensorSpecIso (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom

@[reassoc] lemma infinityIso_inv_base : (infinityIso c).inv ≫ projection c=
    Spec.map (CommRingCat.ofHom
      (algebraMap OriginalLaurentProjectiveOverlap318.Ring (infinityRing c))) := by
  rw [infinityIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_fst]
  exact tensorSpecIso_inv_base (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom

@[reassoc] lemma infinityIso_inv_chart : (infinityIso c).inv ≫ infinityEdge c=
    Spec.map (CommRingCat.ofHom (infinityRight c)) := by
  rw [infinityIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_snd]
  exact tensorSpecIso_inv_chart (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom
end ContactOverlapTensorCharts318
