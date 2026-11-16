module
public import IntegralSectionPencilDegree318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace IntegralPencilChartFlat318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralPencilScalarMaps318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- Flatness of the actual scaled-square affine map follows from the free
monic quadratic algebra in its explicit factorization. -/
instance square_flat (a : Rˣ) :
    Flat (Spec.map (CommRingCat.ofHom (UnitSquarePolynomialFinite318.squareCoordinate a).toRingHom)) := by
  letI : Module.Free R[X] (LinearRootCoordinate318.Root a 0) :=
    FourRootOrder318.root_free (LinearRootCoordinate318.parameter a 0)
  letI : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap R[X] (LinearRootCoordinate318.Root a 0)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [UnitSquarePolynomialFinite318.factor,CommRingCat.ofHom_comp,Spec.map_comp]
  change Flat (Spec.map (LinearRootCoordinate318.coordinateEquiv a 0).toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R[X] (LinearRootCoordinate318.Root a 0))))
  infer_instance

variable (R) (c : Fin 4 → Rˣ)
instance finite_chart_flat : Flat (Spec.map (CommRingCat.ofHom (finiteCoordinate R c).toRingHom)) := by
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R c)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [show (finiteCoordinate R c).toRingHom=(algebraMap R[X] (FiniteOrder R c)).comp
    (UnitSquarePolynomialFinite318.squareCoordinate (c 0)).toRingHom from
      UnitSquarePolynomialFinite318.evaluate_factor (c 0) (FiniteOrder R c),
    CommRingCat.ofHom_comp,Spec.map_comp]
  infer_instance
instance reciprocal_chart_flat : Flat (Spec.map (CommRingCat.ofHom (reciprocalCoordinate R c).toRingHom)) := by
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R c)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [show (reciprocalCoordinate R c).toRingHom=(algebraMap R[X] (InfinityOrder R c)).comp
    (UnitSquarePolynomialFinite318.squareCoordinate (c 0)).toRingHom from
      UnitSquarePolynomialFinite318.evaluate_factor (c 0) (InfinityOrder R c),
    CommRingCat.ofHom_comp,Spec.map_comp]
  infer_instance
end IntegralPencilChartFlat318
