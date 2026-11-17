module
public import ActualTwoDescentActualMordellWeilStructure318
public section
noncomputable section
namespace ActualTwoDescentInfiniteGroupCardinality318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentActualMordellWeilStructure318

/-- Once the actual rational group is infinite, the proved upper bound
forces free rank one and EXACT actual doubling quotient cardinality eight. -/
theorem actual_quotient_eight_of_infinite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hInfinite : Infinite (Point n)) : Nat.card (DoubleQuotient n)=8 := by
  letI := hInfinite
  obtain ⟨r,hr,T,hT,hfin,⟨equiv⟩,hcard⟩ := actual_free_rank_at_most_one n hn hf hbound
  letI := hT
  letI := hfin
  have hr0 : r ≠ 0 := by
    intro he
    subst r
    haveI : Finite ((Fin 0 →₀ ℤ) × T) := inferInstance
    haveI : Finite (Point n) := Finite.of_equiv _ equiv.symm.toEquiv
    exact @Infinite.not_finite (Point n) hInfinite inferInstance
  have hr1 : r=1 := by omega
  simpa only [hr1,pow_one] using hcard

end ActualTwoDescentInfiniteGroupCardinality318
