module
public import ActualTwoDescentInfinityRootUnitFactors318
public section
noncomputable section
namespace ActualTwoDescentInfinityFieldPoleComparison318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityRootUnitFactors318
variable {K L : Type*} [Field K] [CharZero K] [Field L]

/-- Exact algebraic pole-normalization under a specified field map of
the ACTUAL local ring. The field map and nonvanishing of u are explicit:
this does not manufacture an embedding into the original function field. -/
theorem actual_root_function_unit_normalization (n a : K)
    (φ : InfinityLocalRing n →+* L) (hu : φ (localU n) ≠ 0) :
    ∃ e d : (InfinityLocalRing n)ˣ,
      localV n=(e : InfinityLocalRing n)*localU n^3 ∧
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) ∧
      φ (localV n) ≠ 0 ∧
      (φ (localU n)/φ (localV n)-φ (localCoefficient n a))*φ (localU n)^2=
        φ (d : InfinityLocalRing n)/φ (e : InfinityLocalRing n) ∧
      φ (d : InfinityLocalRing n)/φ (e : InfinityLocalRing n) ≠ 0 ∧
      (1/φ (localV n))*φ (localU n)^3=1/φ (e : InfinityLocalRing n) := by
  obtain ⟨e,d,he,hd⟩ := actual_local_root_pole_data n a
  have he0 : φ (e : InfinityLocalRing n) ≠ 0 := (e.isUnit.map φ).ne_zero
  have hd0 : φ (d : InfinityLocalRing n) ≠ 0 := (d.isUnit.map φ).ne_zero
  have hv : φ (localV n)=φ (e : InfinityLocalRing n)*φ (localU n)^3 := by
    rw [he,map_mul,map_pow]
  have hnum : φ (localU n)-φ (localCoefficient n a)*φ (localV n)=
      φ (localU n)*φ (d : InfinityLocalRing n) := by
    simpa only [map_sub,map_mul] using congrArg φ hd
  have hv0 : φ (localV n) ≠ 0 := by rw [hv]; exact mul_ne_zero he0 (pow_ne_zero _ hu)
  refine ⟨e,d,he,hd,hv0,?_,div_ne_zero hd0 he0,?_⟩
  · calc
      (φ (localU n)/φ (localV n)-φ (localCoefficient n a))*φ (localU n)^2=
          ((φ (localU n)-φ (localCoefficient n a)*φ (localV n))/φ (localV n))*
            φ (localU n)^2 := by field_simp [hv0] <;> ring
      _ = _ := by rw [hnum,hv]; field_simp [he0,hu] <;> ring
  · rw [hv]
    field_simp [he0,hu]

end ActualTwoDescentInfinityFieldPoleComparison318
