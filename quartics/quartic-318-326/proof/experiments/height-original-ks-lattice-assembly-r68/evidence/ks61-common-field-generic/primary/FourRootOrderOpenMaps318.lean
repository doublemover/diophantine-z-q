module
public import IntegralWholeReciprocalLocalization318
public section
noncomputable section
namespace FourRootOrderOpenMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318
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

end FourRootOrderOpenMaps318
