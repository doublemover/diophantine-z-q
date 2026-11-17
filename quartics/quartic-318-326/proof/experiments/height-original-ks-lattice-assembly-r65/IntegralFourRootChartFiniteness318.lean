module
public import IntegralFourRootProjectiveProjection318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace IntegralFourRootChartFiniteness318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralFourRootReciprocalCharts318
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

instance finite_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R[X] (FiniteOrder d a)))) := by
  letI : Module.Finite R[X] (FiniteOrder d a) := (finite_chart_free d a).1
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance reciprocal_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R[X] (ReciprocalOrder d a)))) := by
  letI : Module.Finite R[X] (ReciprocalOrder d a) := (reciprocal_chart_free d a).1
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

end IntegralFourRootChartFiniteness318
