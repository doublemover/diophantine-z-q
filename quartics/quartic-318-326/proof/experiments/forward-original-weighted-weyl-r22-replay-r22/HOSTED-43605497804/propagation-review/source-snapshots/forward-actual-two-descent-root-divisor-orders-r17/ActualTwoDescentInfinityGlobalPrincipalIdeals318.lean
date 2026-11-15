module
public import ActualTwoDescentInfinityGlobalRootUnits318
public section
noncomputable section
namespace ActualTwoDescentInfinityGlobalPrincipalIdeals318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityMaximalGenerator318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentInfinityGlobalFactorUnit318 ActualTwoDescentInfinityGlobalRootUnits318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_span_unit_multiple {T : Type*} [CommRing T] (x : T) (e : Tˣ) :
    Ideal.span {x*(e : T)}=Ideal.span {x} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    have he := Set.mem_singleton_iff.mp ha
    subst a
    rw [Ideal.mem_span_singleton]
    exact ⟨e,rfl⟩
  · apply Ideal.span_le.mpr
    intro a ha
    have he := Set.mem_singleton_iff.mp ha
    subst a
    rw [Ideal.mem_span_singleton]
    refine ⟨(e⁻¹ : Tˣ),?_⟩
    rw [mul_assoc,Units.mul_inv,mul_one]

/-- The actual origin ideal is principal on the WHOLE infinity chart,
not merely after localization at the origin. -/
theorem actual_global_origin_principal (n : K) : originIdeal n=Ideal.span {chartU n} := by
  rw [actual_origin_ideal_generators]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl|ha
    · exact Ideal.subset_span (Set.mem_singleton _)
    · have he := Set.mem_singleton_iff.mp ha
      subst a
      rw [actual_global_v_unit_cube,Ideal.mem_span_singleton]
      refine ⟨(globalCubeUnit n : InfinityChart n)*chartU n^2,?_⟩
      ring
  · apply Ideal.span_mono
    intro a ha
    have he := Set.mem_singleton_iff.mp ha
    subst a
    simp

/-- Every actual root numerator cuts out precisely the SAME principal
origin ideal on this chart, with no other affine-chart zeros hidden. -/
theorem actual_global_root_numerator_ideal (n : K) (i : Fin 3) :
    Ideal.span {chartU n-chartCoefficient n (root n i)*chartV n}=originIdeal n := by
  rw [actual_global_origin_principal,actual_global_root_numerator,
    ←actual_global_root_unit_value]
  exact actual_span_unit_multiple _ _

lemma actual_global_v_ideal (n : K) :
    Ideal.span {chartV n}=Ideal.span {chartU n^3} := by
  rw [actual_global_v_unit_cube,mul_comm]
  exact actual_span_unit_multiple _ _
end ActualTwoDescentInfinityGlobalPrincipalIdeals318
