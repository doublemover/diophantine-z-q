module
public import ActualOriginalGlobalSingularSeries318
public import Mathlib.MeasureTheory.Constructions.Pi
public section
noncomputable section
namespace ActualOriginalCoordinateIndex318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalCoordinateFrequency318 MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- A literal2+2+1 indexing of the five original coordinates. -/
abbrev Index := Fin 2 ⊕ (Fin 2 ⊕ Unit)

@[expose] def coordinateEquiv (R : Type*) [MeasurableSpace R] : (Index → R) ≃ᵐ Coordinates R :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Index => R)).trans
    ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => R)).prodCongr
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Unit => R)).trans
        ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => R)).prodCongr
          (MeasurableEquiv.funUnique Unit R))))

lemma actual_coordinate_index_apply (R : Type*) [MeasurableSpace R] (x : Index → R) :
    coordinateEquiv R x =
      ((x (.inl 0),x (.inl 1)),(x (.inr (.inl 0)),x (.inr (.inl 1))),x (.inr (.inr ()))) := rfl

lemma actual_coordinate_index_continuous (R : Type*) [MeasurableSpace R] [TopologicalSpace R] :
    Continuous (coordinateEquiv R) := by
  simp only [actual_coordinate_index_apply]
  fun_prop

/-- This coordinate regrouping preserves the original product Haar
measure exactly. No appeal to an unspecified Euclidean normalization. -/
theorem actual_coordinate_index_measure_preserving :
    MeasurePreserving (coordinateEquiv ℝ) := by
  have htwo := volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  have hone := volume_preserving_funUnique Unit ℝ
  have hi := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Unit => ℝ)
  have ho := volume_measurePreserving_sumPiEquivProdPi (fun _ : Index => ℝ)
  exact (htwo.prod ((htwo.prod hone).comp hi)).comp ho

lemma actual_coordinate_index_add (x y : Index → ℝ) :
    coordinateEquiv ℝ (x+y)=coordinateEquiv ℝ x+coordinateEquiv ℝ y := by
  simp only [actual_coordinate_index_apply]
  rfl

lemma actual_coordinate_index_integer (z : Index → ℤ) :
    coordinateEquiv ℝ (fun i => (z i : ℝ)) = integerEmbed (coordinateEquiv ℤ z) := rfl

lemma actual_coordinate_index_dot (x y : Index → ℝ) :
    dot (coordinateEquiv ℝ x) (coordinateEquiv ℝ y) = ∑ i : Index, x i*y i := by
  simp only [actual_coordinate_index_apply,dot,Fintype.sum_sum_type,Fin.sum_univ_two,
    Fintype.sum_unique]
  ring

lemma actual_coordinate_index_zero : coordinateEquiv ℝ 0 = 0 := rfl

end ActualOriginalCoordinateIndex318
