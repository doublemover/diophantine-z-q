module
public import ActualTwoDescentOriginalInfinityNamedPoleRebuild318
public section
noncomputable section
namespace ActualTwoDescentInfinityPrimeSupportRebuild318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityMaximalGenerator318
variable {K : Type*} [Field K] [CharZero K]

/-- Every prime over v is the ACTUAL infinity origin, including all
non-rational scheme points. -/
theorem support (n : K) (P : Ideal (InfinityChart n)) [P.IsPrime] :
    chartV n ∈ P ↔ P=originIdeal n := by
  constructor
  · intro hv
    have hu3 : chartU n^3 ∈ P := by
      rw [←actual_chart_cubic_relation]
      exact P.mul_mem_right _ hv
    have hu : chartU n ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 3 hu3
    have hle : originIdeal n ≤ P := by
      rw [actual_origin_ideal_generators]
      apply Ideal.span_le.mpr
      intro r hr
      rcases Set.mem_insert_iff.mp hr with rfl|hr
      · exact hu
      · have he := Set.mem_singleton_iff.mp hr
        subst r
        exact hv
    exact ((originIdealMaximal n).eq_of_le
      (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)) hle).symm
  · rintro rfl
    change originEvaluation n (chartV n)=0
    exact actual_origin_v n
end ActualTwoDescentInfinityPrimeSupportRebuild318
