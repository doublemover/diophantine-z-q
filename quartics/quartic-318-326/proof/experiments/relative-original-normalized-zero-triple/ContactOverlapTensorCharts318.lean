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

/-- The reciprocal tensor uses u↦T⁻¹, not the finite-chart action u↦T. -/
abbrev infinityRing :=
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  OriginalLaurentProjectiveOverlap318.Ring ⊗[Polynomial ℚ] ContactWholeInfinityAlgebra318.Ring c

/-- Export the SAME reciprocal tensor carrier structures. The polynomial
base action stays local here, so the finite Laurent action is not replaced. -/
@[expose] instance infinityRing_commRing : CommRing (infinityRing c) := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact Algebra.TensorProduct.instCommRing (R := Polynomial ℚ)
    (A := OriginalLaurentProjectiveOverlap318.Ring) (B := ContactWholeInfinityAlgebra318.Ring c)
@[expose] instance infinityRing_laurentAlgebra :
    Algebra OriginalLaurentProjectiveOverlap318.Ring (infinityRing c) := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact Algebra.TensorProduct.leftAlgebra (R := Polynomial ℚ)
    (S := OriginalLaurentProjectiveOverlap318.Ring)
    (A := OriginalLaurentProjectiveOverlap318.Ring) (B := ContactWholeInfinityAlgebra318.Ring c)

@[expose] def infinityIso : scheme c ≅ Spec (CommRingCat.of (infinityRing c)) := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact (infinity_cartesian c).isoPullback ≪≫ pullbackSpecIso (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactWholeInfinityAlgebra318.Ring c)

@[reassoc] lemma infinityIso_inv_base :
    letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
    (infinityIso c).inv ≫ projection c = Spec.map (CommRingCat.ofHom
      (algebraMap OriginalLaurentProjectiveOverlap318.Ring (infinityRing c))) := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  rw [infinityIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactWholeInfinityAlgebra318.Ring c)

@[reassoc] lemma infinityIso_inv_chart :
    letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
    (infinityIso c).inv ≫ infinityEdge c = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R:=Polynomial ℚ)
        (A:=OriginalLaurentProjectiveOverlap318.Ring)
        (B:=ContactWholeInfinityAlgebra318.Ring c)).toRingHom) := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  rw [infinityIso,Iso.trans_inv,Category.assoc,IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd (Polynomial ℚ)
    OriginalLaurentProjectiveOverlap318.Ring (ContactWholeInfinityAlgebra318.Ring c)
end ContactOverlapTensorCharts318
