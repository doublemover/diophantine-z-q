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
universe u
section Generic
variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- Build the actual tensor inclusion followed by the actual four-root
base-change equivalence on abstract carriers, before specializing a
Laurent carrier with two competing polynomial scalar actions. -/
@[expose] def baseChangedOrderMap (a : Fin 4 → A) :
    FourRootOrder318.Order a →+*
      FourRootOrder318.Order (fun i => algebraMap A T (a i)) :=
  (FourRootOrder318.baseChange a T).toRingHom.comp
    (Algebra.TensorProduct.includeRight : FourRootOrder318.Order a →ₐ[A]
      T ⊗[A] FourRootOrder318.Order a).toRingHom

/-- Prove the open-immersion composition on abstract tensor carriers, before
specializing the large concrete four-root equivalence. -/
private lemma tensor_equiv_open {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] (e : T ⊗[A] B ≃+* C) (x : A) [IsLocalization.Away x T] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom))) := by
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
  rw [h]
  infer_instance

lemma baseChangedOrderMap_open (a : Fin 4 → A) (x : A)
    [IsLocalization.Away x T] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (baseChangedOrderMap (T:=T) a))) := by
  exact tensor_equiv_open (FourRootOrder318.baseChange a T).toRingEquiv x

@[expose] def baseChangedOrderMapAlong (f : A →+* T) (a : Fin 4 → A) :
    FourRootOrder318.Order a →+* FourRootOrder318.Order (fun i => f (a i)) := by
  letI : Algebra A T := f.toAlgebra
  exact baseChangedOrderMap (T:=T) a

lemma baseChangedOrderMapAlong_open (f : A →+* T) (a : Fin 4 → A) (x : A)
    (hl : letI : Algebra A T := f.toAlgebra; IsLocalization.Away x T) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (baseChangedOrderMapAlong f a))) := by
  letI : Algebra A T := f.toAlgebra
  letI : IsLocalization.Away x T := hl
  exact baseChangedOrderMap_open (T:=T) a x
end Generic

variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
abbrev CommonOrder := FourRootOrder318.Order (finiteParameter R d a)

@[expose] def finiteMap : FiniteOrder R d a →+* CommonOrder R d a :=
  baseChangedOrderMap (T := Laurent R) (DVRNormalizedFiniteOrder318.coefficient R d a)

instance finiteMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteMap R d a))) :=
  baseChangedOrderMap_open (T := Laurent R)
    (DVRNormalizedFiniteOrder318.coefficient R d a) (X : R[X])

section ReciprocalScalar
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) :=
  (reciprocalMap R).toRingHom.toAlgebra

@[expose] def infinityMap : InfinityOrder R d a →+* CommonOrder R d a :=
  (fullOverlap R d a).symm.toRingHom.comp
    (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
      (DVRNormalizedInfinityOrder318.coefficient R d a))

/-- The FULL reciprocal punctured source is an open immersion. The only
inverted base element is its coordinate, not the branch-factor product. -/
instance infinityMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityMap R d a))) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
        (DVRNormalizedInfinityOrder318.coefficient R d a)))) :=
    baseChangedOrderMapAlong_open (reciprocalMap R).toRingHom
      (DVRNormalizedInfinityOrder318.coefficient R d a) (X : R[X])
      (NormalizedReciprocalLaurent318.reciprocal_localization R)
  have h : Spec.map (CommRingCat.ofHom (infinityMap R d a)) =
      Spec.map (fullOverlap R d a).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
          (DVRNormalizedInfinityOrder318.coefficient R d a))) := by
    rw [←Spec.map_comp]
    rfl
  rw [h]
  infer_instance
end ReciprocalScalar
end NormalizedWholeOpenMaps318
