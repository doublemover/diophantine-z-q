module
public import IntegralWholeReciprocalLocalization318
public section
noncomputable section
namespace IntegralWholeOrderOpenMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
abbrev CommonOrder := ThreeRootOrder318.Order (finiteParameter R c)

@[expose] def finiteMap : FiniteOrder R c →+* CommonOrder R c :=
  (finiteBaseChange R c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : FiniteOrder R c →ₐ[R[X]]
      Laurent R ⊗[R[X]] FiniteOrder R c).toRingHom

instance finiteMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteMap R c))) := by
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
  rw [h]
  infer_instance

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R c).toRingHom.toAlgebra

@[expose] def infinityMap : InfinityOrder R c →+* CommonOrder R c :=
  (fullOverlap R c).symm.toRingHom.comp
    ((infinityBaseChange R c).toRingHom.comp
      (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
        Laurent R ⊗[R[X]] InfinityOrder R c).toRingHom)

/-- The FULL reciprocal punctured source is an open immersion. The only
inverted base element is its coordinate, not the branch-factor product. -/
instance infinityMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityMap R c))) := by
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
  rw [h]
  infer_instance
end ReciprocalScalar
end IntegralWholeOrderOpenMaps318
