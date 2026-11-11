module
public import UnitSquarePolynomialFinite318
public section
noncomputable section
namespace IntegralPencilChartFiniteness318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralPencilScalarMaps318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

instance finite_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom (finiteCoordinate R c).toRingHom)) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R c)))) :=
    IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [show (finiteCoordinate R c).toRingHom=(algebraMap R[X] (FiniteOrder R c)).comp
    (UnitSquarePolynomialFinite318.squareCoordinate (c 0)).toRingHom from
      UnitSquarePolynomialFinite318.evaluate_factor (c 0) (FiniteOrder R c),
    CommRingCat.ofHom_comp,Spec.map_comp]
  infer_instance

instance reciprocal_chart_finite :
    IsFinite (Spec.map (CommRingCat.ofHom (reciprocalCoordinate R c).toRingHom)) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R c)))) :=
    IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [show (reciprocalCoordinate R c).toRingHom=(algebraMap R[X] (InfinityOrder R c)).comp
    (UnitSquarePolynomialFinite318.squareCoordinate (c 0)).toRingHom from
      UnitSquarePolynomialFinite318.evaluate_factor (c 0) (InfinityOrder R c),
    CommRingCat.ofHom_comp,Spec.map_comp]
  infer_instance
end IntegralPencilChartFiniteness318
