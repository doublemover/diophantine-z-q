module
public import IntegralWholeChartFiniteness318
public section
noncomputable section
namespace IntegralWholeOpenRanges318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section Generic
variable {A T B C : Type u} [CommRing A] [CommRing T] [CommRing B] [CommRing C]
  [Algebra A T] [Algebra A B]

/-- Compute the actual open range before specializing the large original
three-root carriers and their two distinct Laurent scalar structures. -/
private lemma tensor_equiv_range (e : T ⊗[A] B ≃+* C) (x : A)
    [IsLocalization.Away x T]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)))] :
    (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap A B x) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra A T B
  letI := IntegralInfinityOverlapRealization318.baseChange_localization A T B x
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap A B x)
  have h : Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)) =
      Spec.map e.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (T ⊗[A] B) (algebraMap A B x)

lemma baseChangedOrderMap_range (a : Fin 3 → A) (x : A) [IsLocalization.Away x T] :
    letI := baseChangedOrderMap_open (T:=T) a x
    (Spec.map (CommRingCat.ofHom (baseChangedOrderMap (T:=T) a))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap A (ThreeRootOrder318.Order a) x) := by
  letI := baseChangedOrderMap_open (T:=T) a x
  exact tensor_equiv_range (ThreeRootOrder318.baseChange a T).toRingEquiv x

lemma baseChangedOrderMapAlong_range (f : A →+* T) (a : Fin 3 → A) (x : A)
    (hl : letI : Algebra A T := f.toAlgebra; IsLocalization.Away x T) :
    letI := baseChangedOrderMapAlong_open f a x hl
    (Spec.map (CommRingCat.ofHom (baseChangedOrderMapAlong f a))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap A (ThreeRootOrder318.Order a) x) := by
  letI : Algebra A T := f.toAlgebra
  letI : IsLocalization.Away x T := hl
  exact baseChangedOrderMap_range (T:=T) a x
end Generic

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_range :
    (Spec.map (CommRingCat.ofHom (finiteMap R c))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (FiniteOrder R c) X) := by
  exact baseChangedOrderMap_range (T:=Laurent R) (finiteCoefficient R c) (X:R[X])

section ReciprocalScalar

theorem infinity_range :
    (Spec.map (CommRingCat.ofHom (infinityMap R c))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (InfinityOrder R c) X) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (baseChangedOrderMapAlong (reciprocalMap R c).toRingHom
        (IntegralInfinityChart318.coefficient R c)))) :=
    baseChangedOrderMapAlong_open (reciprocalMap R c).toRingHom
      (IntegralInfinityChart318.coefficient R c) (X:R[X])
      (IntegralWholeReciprocalLocalization318.reciprocal_localization R c)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R c)) =
      Spec.map (fullOverlap R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (baseChangedOrderMapAlong (reciprocalMap R c).toRingHom
          (IntegralInfinityChart318.coefficient R c))) := by
    rw [←Spec.map_comp]
    rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso]
  exact baseChangedOrderMapAlong_range (reciprocalMap R c).toRingHom
    (IntegralInfinityChart318.coefficient R c) (X:R[X])
    (IntegralWholeReciprocalLocalization318.reciprocal_localization R c)
end ReciprocalScalar
end IntegralWholeOpenRanges318
