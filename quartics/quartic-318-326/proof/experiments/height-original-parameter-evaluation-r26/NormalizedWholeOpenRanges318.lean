module
public import NormalizedWholeChartFinite318
public section
noncomputable section
namespace NormalizedWholeOpenRanges318
open Polynomial AlgebraicGeometry CategoryTheory
open NormalizedWholeOverlap318 NormalizedReciprocalLaurent318 NormalizedWholeOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section Generic
variable {A T B C : Type u} [CommRing A] [CommRing T] [CommRing B] [CommRing C]
variable [Algebra A T] [Algebra A B]

/-- Compute the localization range on symbolic carriers, before substituting
large four-root tensors or the two different Laurent coefficient actions. -/
private theorem tensor_equiv_range (e : T ⊗[A] B ≃+* C) (x : A)
    [IsLocalization.Away x T] :
    Set.range (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom))) =
        PrimeSpectrum.basicOpen (algebraMap A B x) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra A T B
  letI := IntegralInfinityOverlapRealization318.baseChange_localization A T B x
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap A B x)
  have h : Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)) =
      Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [h]
  change (((Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom))).opensRange :
      Set (Spec (CommRingCat.of B))) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact PrimeSpectrum.localization_away_comap_range (T ⊗[A] B) (algebraMap A B x)

private theorem baseChangedOrderMap_range (a : Fin 4 → A) (x : A)
    [IsLocalization.Away x T] :
    Set.range (Spec.map (CommRingCat.ofHom (baseChangedOrderMap (T := T) a))) =
      PrimeSpectrum.basicOpen (algebraMap A (FourRootOrder318.Order a) x) :=
  tensor_equiv_range (FourRootOrder318.baseChange a T).toRingEquiv x

private theorem baseChangedOrderMapAlong_range (f : A →+* T) (a : Fin 4 → A) (x : A)
    (hl : letI : Algebra A T := f.toAlgebra; IsLocalization.Away x T) :
    Set.range (Spec.map (CommRingCat.ofHom (baseChangedOrderMapAlong f a))) =
      PrimeSpectrum.basicOpen (algebraMap A (FourRootOrder318.Order a) x) := by
  letI : Algebra A T := f.toAlgebra
  letI : IsLocalization.Away x T := hl
  exact baseChangedOrderMap_range (T := T) a x
end Generic

variable (R : Type*) [CommRing R] (d contacts : Fin 4 → R)

theorem finite_range :
    (Spec.map (CommRingCat.ofHom (finiteMap R d contacts))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap R[X] (FiniteOrder R d contacts) X) := by
  apply TopologicalSpace.Opens.ext
  exact baseChangedOrderMap_range (T := Laurent R)
    (DVRNormalizedFiniteOrder318.coefficient R d contacts) (X : R[X])

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R).toRingHom.toAlgebra

theorem infinity_range :
    (Spec.map (CommRingCat.ofHom (infinityMap R d contacts))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap R[X] (InfinityOrder R d contacts) X) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
        (DVRNormalizedInfinityOrder318.coefficient R d contacts)))) :=
    baseChangedOrderMapAlong_open (reciprocalMap R).toRingHom
      (DVRNormalizedInfinityOrder318.coefficient R d contacts) (X : R[X])
      (NormalizedReciprocalLaurent318.reciprocal_localization R)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R d contacts)) =
      Spec.map (fullOverlap R d contacts).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
          (DVRNormalizedInfinityOrder318.coefficient R d contacts))) := by
    rw [← Spec.map_comp]
    rfl
  rw [h, Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact baseChangedOrderMapAlong_range (reciprocalMap R).toRingHom
    (DVRNormalizedInfinityOrder318.coefficient R d contacts) (X : R[X])
    (NormalizedReciprocalLaurent318.reciprocal_localization R)
end ReciprocalScalar
end NormalizedWholeOpenRanges318
