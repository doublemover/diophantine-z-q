module
public import ActualTwoDescentRationalImageCardinality318
public section
noncomputable section
namespace ActualTwoDescentRationalQuotientAlternative318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentActualMordellWeilStructure318 ActualTwoDescentDoublingIndexTransport318
open ActualTwoDescentActualTwoTorsionCardinality318 ActualTwoDescentInfiniteGroupCardinality318

lemma actual_quotient_four_of_finite (n : ℚ) (hn : n ≠ 0) (hf : Finite (Point n)) :
    Nat.card (DoubleQuotient n)=4 := by
  letI := hf
  rw [←actual_tagged_doubles_index]
  change (nsmulAddMonoidHom (α:=Point n) 2).range.index=4
  rw [AddSubgroup.index_range]
  exact actual_doubling_kernel_card n hn

/-- The actual rational quotient has cardinality four or eight, never an inferred local count. -/
theorem actual_quotient_four_or_eight (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n))
    (hbound : Nat.card (DoubleQuotient n) ≤ 8) :
    Nat.card (DoubleQuotient n)=4 ∨ Nat.card (DoubleQuotient n)=8 := by
  obtain ⟨r,hr,T,hT,hfin,he,hcard⟩ := actual_free_rank_at_most_one n hn hf hbound
  have hcases : r=0 ∨ r=1 := by omega
  rcases hcases with h0|h1
  · left; simpa only [h0,pow_zero,one_mul] using hcard
  · right; simpa only [h1,pow_one] using hcard

lemma actual_infinite_of_quotient_eight (n : ℚ) (hn : n ≠ 0)
    (hcard : Nat.card (DoubleQuotient n)=8) : Infinite (Point n) := by
  constructor
  intro hf
  have hfour := actual_quotient_four_of_finite n hn hf
  omega

lemma actual_finite_of_quotient_four (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n))
    (hbound : Nat.card (DoubleQuotient n) ≤ 8) (hcard : Nat.card (DoubleQuotient n)=4) : Finite (Point n) := by
  obtain ⟨r,hr,T,hT,hfin,⟨e⟩,hindex⟩ := actual_free_rank_at_most_one n hn hf hbound
  have hr0 : r=0 := by
    have hcases : r=0 ∨ r=1 := by omega
    rcases hcases with h|h
    · exact h
    · simp only [h,pow_one] at hindex
      omega
  subst r
  letI := hT
  letI := hfin
  exact Finite.of_equiv ((Fin 0 →₀ ℤ) × T) e.symm.toEquiv

theorem actual_infinite_iff_quotient_eight (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8) :
    Infinite (Point n) ↔ Nat.card (DoubleQuotient n)=8 :=
  ⟨actual_quotient_eight_of_infinite n hn hf hbound,actual_infinite_of_quotient_eight n hn⟩

end ActualTwoDescentRationalQuotientAlternative318
