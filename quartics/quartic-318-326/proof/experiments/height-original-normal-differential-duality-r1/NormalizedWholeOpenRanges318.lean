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
variable (R : Type*) [CommRing R] (d contacts : Fin 4 → R)

theorem finite_range :
    (Spec.map (CommRingCat.ofHom (finiteMap R d contacts))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (FiniteOrder R d contacts) X) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (FiniteOrder R d contacts)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (FiniteOrder R d contacts) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : FiniteOrder R d contacts →ₐ[R[X]]
        Laurent R ⊗[R[X]] FiniteOrder R d contacts).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (FiniteOrder R d contacts) X)
  have h : Spec.map (CommRingCat.ofHom (finiteMap R d contacts))=
      Spec.map (finiteBaseChange R d contacts).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : FiniteOrder R d contacts →ₐ[R[X]]
          Laurent R ⊗[R[X]] FiniteOrder R d contacts).toRingHom) := by
    rw [←Spec.map_comp]
    all_goals rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (Laurent R ⊗[R[X]] FiniteOrder R d contacts) (algebraMap R[X] (FiniteOrder R d contacts) X)

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R).toRingHom.toAlgebra

theorem infinity_range :
    (Spec.map (CommRingCat.ofHom (infinityMap R d contacts))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (InfinityOrder R d contacts) X) := by
  letI := NormalizedReciprocalLaurent318.reciprocal_localization R
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (InfinityOrder R d contacts)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (InfinityOrder R d contacts) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : InfinityOrder R d contacts →ₐ[R[X]]
        Laurent R ⊗[R[X]] InfinityOrder R d contacts).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (InfinityOrder R d contacts) X)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R d contacts))=
      Spec.map (fullOverlap R d contacts).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (infinityBaseChange R d contacts).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : InfinityOrder R d contacts →ₐ[R[X]]
          Laurent R ⊗[R[X]] InfinityOrder R d contacts).toRingHom) := by
    rw [←Spec.map_comp,←Spec.map_comp]
    all_goals rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (Laurent R ⊗[R[X]] InfinityOrder R d contacts) (algebraMap R[X] (InfinityOrder R d contacts) X)
end ReciprocalScalar
end NormalizedWholeOpenRanges318
