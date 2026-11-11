module
public import NormalizedWholeOverlap318
public section
noncomputable section
namespace NormalizedWholeOpenMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open NormalizedWholeOverlap318 NormalizedReciprocalLaurent318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
abbrev CommonOrder := FourRootOrder318.Order (finiteParameter R d a)

@[expose] def finiteMap : FiniteOrder R d a →+* CommonOrder R d a :=
  (finiteBaseChange R d a).toRingHom.comp
    (Algebra.TensorProduct.includeRight : FiniteOrder R d a →ₐ[R[X]]
      Laurent R ⊗[R[X]] FiniteOrder R d a).toRingHom

instance finiteMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteMap R d a))) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (FiniteOrder R d a)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (FiniteOrder R d a) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : FiniteOrder R d a →ₐ[R[X]]
        Laurent R ⊗[R[X]] FiniteOrder R d a).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (FiniteOrder R d a) X)
  have h : Spec.map (CommRingCat.ofHom (finiteMap R d a))=
      Spec.map (finiteBaseChange R d a).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : FiniteOrder R d a →ₐ[R[X]]
          Laurent R ⊗[R[X]] FiniteOrder R d a).toRingHom) := by
    rw [←Spec.map_comp]
    all_goals rfl
  rw [h]
  infer_instance

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R).toRingHom.toAlgebra

@[expose] def infinityMap : InfinityOrder R d a →+* CommonOrder R d a :=
  (fullOverlap R d a).symm.toRingHom.comp
    ((infinityBaseChange R d a).toRingHom.comp
      (Algebra.TensorProduct.includeRight : InfinityOrder R d a →ₐ[R[X]]
        Laurent R ⊗[R[X]] InfinityOrder R d a).toRingHom)

/-- The FULL reciprocal punctured source is an open immersion. The only
inverted base element is its coordinate, not the branch-factor product. -/
instance infinityMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityMap R d a))) := by
  letI := NormalizedReciprocalLaurent318.reciprocal_localization R
  letI := IntegralInfinityOverlapRealization318.rightAlgebra R[X] (Laurent R) (InfinityOrder R d a)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (Laurent R) (InfinityOrder R d a) (X:R[X])
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : InfinityOrder R d a →ₐ[R[X]]
        Laurent R ⊗[R[X]] InfinityOrder R d a).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap R[X] (InfinityOrder R d a) X)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R d a))=
      Spec.map (fullOverlap R d a).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (infinityBaseChange R d a).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : InfinityOrder R d a →ₐ[R[X]]
          Laurent R ⊗[R[X]] InfinityOrder R d a).toRingHom) := by
    rw [←Spec.map_comp,←Spec.map_comp]
    all_goals rfl
  rw [h]
  infer_instance
end ReciprocalScalar
end NormalizedWholeOpenMaps318
