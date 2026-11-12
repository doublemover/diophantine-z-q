module
public import NormalizedWholeProjection318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace NormalizedWholeChartFinite318
open Polynomial AlgebraicGeometry CategoryTheory NormalizedWholeOverlap318
set_option maxHeartbeats 700000
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
instance finite_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R[X] (FiniteOrder R d a)))) := by
  letI : Module.Finite R[X] (FiniteOrder R d a) := (DVRNormalizedFiniteOrder318.finite_free R d a).1
  exact IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)
instance infinity_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R[X] (InfinityOrder R d a)))) := by
  letI : Module.Finite R[X] (InfinityOrder R d a) := (DVRNormalizedInfinityOrder318.finite_free R d a).1
  exact IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)
end NormalizedWholeChartFinite318
