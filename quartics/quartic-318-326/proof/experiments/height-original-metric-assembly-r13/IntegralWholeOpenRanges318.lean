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
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_range :
    (Spec.map (CommRingCat.ofHom (finiteMap R c))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (FiniteOrder R c) X) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (FiniteOrder R c)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (FiniteOrder R c) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : FiniteOrder R c →ₐ[R[X]]
        Laurent R ⊗[R[X]] FiniteOrder R c).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (FiniteOrder R c) X)
  have h : Spec.map (CommRingCat.ofHom (finiteMap R c))=
      Spec.map (finiteBaseChange R c).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : FiniteOrder R c →ₐ[R[X]]
          Laurent R ⊗[R[X]] FiniteOrder R c).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (Laurent R ⊗[R[X]] FiniteOrder R c) (algebraMap R[X] (FiniteOrder R c) X)

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R c).toRingHom.toAlgebra

theorem infinity_range :
    (Spec.map (CommRingCat.ofHom (infinityMap R c))).opensRange=
      PrimeSpectrum.basicOpen (algebraMap R[X] (InfinityOrder R c) X) := by
  letI := IntegralWholeReciprocalLocalization318.reciprocal_localization R c
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (InfinityOrder R c)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (InfinityOrder R c) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
        Laurent R ⊗[R[X]] InfinityOrder R c).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (InfinityOrder R c) X)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R c))=
      Spec.map (fullOverlap R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (infinityBaseChange R c).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
          Laurent R ⊗[R[X]] InfinityOrder R c).toRingHom) := by
    rw [←Spec.map_comp,←Spec.map_comp]
    rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (Laurent R ⊗[R[X]] InfinityOrder R c) (algebraMap R[X] (InfinityOrder R c) X)
end ReciprocalScalar
end IntegralWholeOpenRanges318
