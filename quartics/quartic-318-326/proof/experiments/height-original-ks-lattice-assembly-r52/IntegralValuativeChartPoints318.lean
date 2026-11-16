module
public import IntegralValuativeRootCoordinates318
public import IntegralRootPointMaps318
public import IntegralGluedModel318
public section
noncomputable section
namespace IntegralValuativeChartPoints318
open Polynomial IntegralSourceBranches318 IntegralRootPointMaps318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V] (c : Fin 4 → Vˣ)
section Finite
variable (a : V) (z : Fin 4 → V) (hz : ∀ i, (z i)^2=(c i : V)*(a-contacts V i))
local instance evaluationAlgebra : Algebra V[X] V := (Polynomial.evalRingHom a).toAlgebra

include hz in
theorem finite_root_relation (i : Fin 4) : (z i)^2=algebraMap V[X] V (coefficient V c i) := by
  simpa only [coefficient,LinearRootCoordinate318.parameter,Polynomial.eval_mul,
    Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X] using hz i

/-- A genuine map from the WHOLE original finite order, including its
ramification points, with the specified integral root values. -/
@[expose] def finiteMap : SourceOrder V c →+* V :=
  (fourMap (coefficient V c) z (finite_root_relation V c a z hz)).toRingHom

theorem finiteMap_polynomial (p : V[X]) :
    finiteMap V c a z hz (algebraMap V[X] (SourceOrder V c) p)=Polynomial.eval a p :=
  (fourMap (coefficient V c) z (finite_root_relation V c a z hz)).commutes p

theorem finiteMap_generator (i : Fin 4) :
    finiteMap V c a z hz (FourRootOrderSigns318.generator (coefficient V c) i)=z i :=
  fourMap_generator _ _ _ i

@[expose] def finitePoint : Spec (CommRingCat.of V) ⟶ IntegralGluedModel318.scheme V c :=
  Spec.map (CommRingCat.ofHom (finiteMap V c a z hz)) ≫ IntegralGluedModel318.finiteChart V c
theorem finitePoint_structure : finitePoint V c a z hz ≫ IntegralGluedModel318.structureMap V c=𝟙 _ := by
  have he : (finiteMap V c a z hz).comp (algebraMap V (SourceOrder V c))=RingHom.id V := by
    apply RingHom.ext
    intro r
    change finiteMap V c a z hz (algebraMap V (SourceOrder V c) r)=r
    rw [IsScalarTower.algebraMap_apply V V[X] (SourceOrder V c)]
    exact (finiteMap_polynomial V c a z hz (C r)).trans (Polynomial.eval_C a r)
  rw [finitePoint,Category.assoc,IntegralGluedModel318.finiteChart_structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((finiteMap V c a z hz).comp (algebraMap V (SourceOrder V c))))=𝟙 _
  rw [he]
  exact Spec.map_id (CommRingCat.of V)
end Finite

section Infinity
variable (u : V) (z : Fin 3 → V)
  (hz : ∀ j, (z j)^2=Polynomial.eval u (IntegralInfinityChart318.coefficient V c j))
  (hu : IsUnit (Polynomial.eval u (IntegralInfinityChart318.denominator V c)))

@[expose] def infinityBaseMap : IntegralInfinityChart318.Base V c →+* V :=
  IsLocalization.Away.lift (g := Polynomial.evalRingHom u)
    (IntegralInfinityChart318.denominator V c) hu

theorem infinityBaseMap_polynomial (p : V[X]) :
    infinityBaseMap V c u hu (algebraMap V[X] (IntegralInfinityChart318.Base V c) p)=Polynomial.eval u p :=
  IsLocalization.Away.lift_eq _ hu p
local instance infinityEvaluationAlgebra : Algebra (IntegralInfinityChart318.Base V c) V :=
  (infinityBaseMap V c u hu).toAlgebra

include hz in
theorem infinity_root_relation (j : Fin 3) :
    (z j)^2=algebraMap (IntegralInfinityChart318.Base V c) V
      (algebraMap V[X] (IntegralInfinityChart318.Base V c) (IntegralInfinityChart318.coefficient V c j)) := by
  change (z j)^2=infinityBaseMap V c u hu
    (algebraMap V[X] (IntegralInfinityChart318.Base V c) (IntegralInfinityChart318.coefficient V c j))
  rw [infinityBaseMap_polynomial]
  exact hz j

/-- A genuine point of the original infinity order, not merely its base or
a triple of unrelated roots. Its coefficient localization is defined because
the actual denominator has been proved a unit. -/
@[expose] def infinityMap : IntegralInfinityChart318.Order V c →+* V :=
  (threeMap (fun j => algebraMap V[X] (IntegralInfinityChart318.Base V c)
    (IntegralInfinityChart318.coefficient V c j)) z (infinity_root_relation V c u z hz hu)).toRingHom

theorem infinityMap_base (b : IntegralInfinityChart318.Base V c) :
    infinityMap V c u z hz hu
      (algebraMap (IntegralInfinityChart318.Base V c) (IntegralInfinityChart318.Order V c) b)=
      infinityBaseMap V c u hu b :=
  (threeMap _ z (infinity_root_relation V c u z hz hu)).commutes b

theorem infinityMap_polynomial (p : V[X]) :
    infinityMap V c u z hz hu (algebraMap V[X] (IntegralInfinityChart318.Order V c) p)=Polynomial.eval u p := by
  rw [IsScalarTower.algebraMap_apply V[X] (IntegralInfinityChart318.Base V c)
    (IntegralInfinityChart318.Order V c),infinityMap_base,infinityBaseMap_polynomial]

theorem infinityMap_generator (j : Fin 3) :
    infinityMap V c u z hz hu
      (ThreeRootCoordinates318.generator (fun k => algebraMap V[X]
        (IntegralInfinityChart318.Base V c) (IntegralInfinityChart318.coefficient V c k)) j)=z j :=
  threeMap_generator _ _ _ j

theorem infinityMap_coordinate :
    infinityMap V c u z hz hu (IntegralInfinityChart318.coordinate V c)=u := by
  rw [IntegralInfinityChart318.coordinate,infinityMap_base,infinityBaseMap_polynomial,Polynomial.eval_X]

@[expose] def infinityPoint : Spec (CommRingCat.of V) ⟶ IntegralGluedModel318.scheme V c :=
  Spec.map (CommRingCat.ofHom (infinityMap V c u z hz hu)) ≫ IntegralGluedModel318.infinityChart V c
theorem infinityPoint_structure : infinityPoint V c u z hz hu ≫ IntegralGluedModel318.structureMap V c=𝟙 _ := by
  have he : (infinityMap V c u z hz hu).comp (algebraMap V (IntegralInfinityChart318.Order V c))=RingHom.id V := by
    apply RingHom.ext
    intro r
    change infinityMap V c u z hz hu (algebraMap V (IntegralInfinityChart318.Order V c) r)=r
    rw [IsScalarTower.algebraMap_apply V V[X] (IntegralInfinityChart318.Order V c)]
    exact (infinityMap_polynomial V c u z hz hu (C r)).trans (Polynomial.eval_C u r)
  rw [infinityPoint,Category.assoc,IntegralGluedModel318.infinityChart_structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((infinityMap V c u z hz hu).comp
    (algebraMap V (IntegralInfinityChart318.Order V c))))=𝟙 _
  rw [he]
  exact Spec.map_id (CommRingCat.of V)
end Infinity
end IntegralValuativeChartPoints318
