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
universe u
section Generic
variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- Build the actual tensor inclusion followed by the actual three-root
base-change equivalence on abstract carriers, before specializing a
Laurent carrier with two competing polynomial scalar actions. -/
@[expose] def baseChangedOrderMap (a : Fin 3 → A) :
    ThreeRootOrder318.Order a →+*
      ThreeRootOrder318.Order (fun i => algebraMap A T (a i)) :=
  (ThreeRootOrder318.baseChange a T).toRingHom.comp
    (Algebra.TensorProduct.includeRight : ThreeRootOrder318.Order a →ₐ[A]
      T ⊗[A] ThreeRootOrder318.Order a).toRingHom

lemma baseChangedOrderMap_open (a : Fin 3 → A) (x : A)
    [IsLocalization.Away x T] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (baseChangedOrderMap (T:=T) a))) := by
  let B := ThreeRootOrder318.Order a
  letI := IntegralInfinityOverlapRealization318.rightAlgebra A T B
  letI := IntegralInfinityOverlapRealization318.baseChange_localization A T B x
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap A B x)
  have h : Spec.map (CommRingCat.ofHom (baseChangedOrderMap (T:=T) a)) =
      Spec.map (ThreeRootOrder318.baseChange a T).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h]
  infer_instance

@[expose] def baseChangedOrderMapAlong (f : A →+* T) (a : Fin 3 → A) :
    ThreeRootOrder318.Order a →+* ThreeRootOrder318.Order (fun i => f (a i)) := by
  letI : Algebra A T := f.toAlgebra
  exact baseChangedOrderMap (T:=T) a

lemma baseChangedOrderMapAlong_open (f : A →+* T) (a : Fin 3 → A) (x : A)
    (hl : letI : Algebra A T := f.toAlgebra; IsLocalization.Away x T) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (baseChangedOrderMapAlong f a))) := by
  letI : Algebra A T := f.toAlgebra
  letI : IsLocalization.Away x T := hl
  exact baseChangedOrderMap_open (T:=T) a x
end Generic

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
abbrev CommonOrder := ThreeRootOrder318.Order (finiteParameter R c)

@[expose] def finiteMap : FiniteOrder R c →+* CommonOrder R c :=
  baseChangedOrderMap (T:=Laurent R) (finiteCoefficient R c)

instance finiteMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteMap R c))) :=
  baseChangedOrderMap_open (T:=Laurent R) (finiteCoefficient R c) (X:R[X])

/-- The same reciprocal tensor inclusion followed by the same base-change
and full-overlap equivalences; its scalar action remains u=c0/y0. -/
@[expose] def infinityMap : InfinityOrder R c →+* CommonOrder R c :=
  (fullOverlap R c).symm.toRingHom.comp
    (baseChangedOrderMapAlong (reciprocalMap R c).toRingHom
      (IntegralInfinityChart318.coefficient R c))

/-- The FULL reciprocal punctured source is an open immersion. The only
inverted base element is its coordinate, not the branch-factor product. -/
instance infinityMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityMap R c))) := by
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
  rw [h]
  infer_instance
end IntegralWholeOrderOpenMaps318
