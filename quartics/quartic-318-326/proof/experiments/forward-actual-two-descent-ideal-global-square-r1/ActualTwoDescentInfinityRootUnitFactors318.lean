module
public import ActualTwoDescentInfinityMaximalGenerator318
public section
noncomputable section
namespace ActualTwoDescentInfinityRootUnitFactors318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_local_one_sub_unit (n : K) (a : InfinityLocalRing n)
    (ha : a ∈ IsLocalRing.maximalIdeal (InfinityLocalRing n)) : IsUnit (1-a) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  have hh := (IsLocalRing.maximalIdeal (InfinityLocalRing n)).add_mem h ha
  have hone : (1 : InfinityLocalRing n) ∈ IsLocalRing.maximalIdeal (InfinityLocalRing n) := by
    simpa only [sub_add_cancel] using hh
  exact (Ideal.IsMaximal.ne_top (inferInstance :
    (IsLocalRing.maximalIdeal (InfinityLocalRing n)).IsMaximal))
    (Ideal.eq_top_iff_one.mpr hone)

/-- Every original affine root numerator u-a*v is u times a unit at O.
The parameter a is arbitrary, hence this covers ALL three original roots. -/
theorem actual_local_root_numerator (n a : K) :
    ∃ d : (InfinityLocalRing n)ˣ,
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) := by
  obtain ⟨e,he⟩ := actual_local_v_unit_cube n
  have hm : localCoefficient n a*(e : InfinityLocalRing n)*localU n^2 ∈
      IsLocalRing.maximalIdeal (InfinityLocalRing n) := by
    have hp := (IsLocalRing.maximalIdeal (InfinityLocalRing n)).mul_mem_left
      (localU n) (actual_local_u_in_maximal n)
    simpa only [pow_two] using
      (IsLocalRing.maximalIdeal (InfinityLocalRing n)).mul_mem_left
        (localCoefficient n a*(e : InfinityLocalRing n)) hp
  obtain ⟨d,hd⟩ := actual_local_one_sub_unit n _ hm
  refine ⟨d,?_⟩
  rw [hd,he]
  ring

/-- Coupled unit data needed for the order-two pole of x-a at O. Neither
normalization of a valuation nor a divisor equality is assumed. -/
theorem actual_local_root_pole_data (n a : K) :
    ∃ e d : (InfinityLocalRing n)ˣ,
      localV n=(e : InfinityLocalRing n)*localU n^3 ∧
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) := by
  obtain ⟨e,he⟩ := actual_local_v_unit_cube n
  obtain ⟨d,hd⟩ := actual_local_root_numerator n a
  exact ⟨e,d,he,hd⟩

end ActualTwoDescentInfinityRootUnitFactors318
