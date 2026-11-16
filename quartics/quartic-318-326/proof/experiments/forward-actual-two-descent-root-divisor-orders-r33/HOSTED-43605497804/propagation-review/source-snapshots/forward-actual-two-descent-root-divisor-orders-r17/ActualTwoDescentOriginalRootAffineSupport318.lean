module
public import ActualTwoDescentOriginalRootNormalizedOrders318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootAffineSupport318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentOriginalRootMaximalIdeal318
variable {K : Type*} [Field K] [CharZero K]

/-- ALL affine primes where the root function vanishes, not only rational points. -/
theorem actual_root_prime_support (n : K) (i : Fin 3)
    (P : Ideal (AffineChart n)) [P.IsPrime] : rootNumerator n i∈P ↔ P=rootIdeal n i := by
  constructor
  · intro hf
    have hy2 : affineY n^2∈P := by
      rw [actual_root_factorization n i]
      exact P.mul_mem_right _ hf
    have hy : affineY n∈P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hy2
    have hle : rootIdeal n i≤P := by
      rw [actual_root_ideal_generators]
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl|ha
      · exact hf
      · have he := Set.mem_singleton_iff.mp ha
        subst a
        exact hy
    exact ((rootIdealMaximal n i).eq_of_le
      (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)) hle).symm
  · rintro rfl
    rw [actual_root_ideal_generators]
    exact Ideal.subset_span (by simp)

/-- Outside that one ACTUAL affine prime the function is a local unit.
No smoothness or DVR assumption is needed for this support statement. -/
theorem actual_root_unit_off_support (n : K) (i : Fin 3)
    (P : Ideal (AffineChart n)) [P.IsPrime] (hP : P≠rootIdeal n i) :
    IsUnit (algebraMap (AffineChart n) (Localization.AtPrime P) (rootNumerator n i)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mpr
  exact fun h => hP ((actual_root_prime_support n i P).mp h)
end ActualTwoDescentOriginalRootAffineSupport318
