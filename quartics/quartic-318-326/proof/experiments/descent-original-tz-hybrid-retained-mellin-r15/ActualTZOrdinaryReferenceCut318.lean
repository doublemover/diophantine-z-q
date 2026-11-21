module
public import Mathlib
public section
noncomputable section
namespace ActualTZOrdinaryReferenceCut318
open scoped BigOperators

/-- The Euler comparison truncation is freely chosen above its
analytic threshold and every actual divisor slot. This is not the
physical sample size and it imposes no new condition on that sample. -/
theorem reference_exists (W : ℕ) (hW : 0<W) (R : ℝ) :
    ∃ P : ℕ,Real.exp ((Real.log R)^2)≤(P:ℝ) ∧
      W.primeFactors⊆Nat.primesBelow (P+1) ∧ ⌊R⌋₊<P+1 := by
  obtain ⟨T,hT⟩ := exists_nat_gt (Real.exp ((Real.log R)^2))
  let P := T+W+⌊R⌋₊
  have hT' : T≤P := by dsimp only [P]; omega
  have hW' : W≤P := by dsimp only [P]; omega
  have hR' : ⌊R⌋₊<P+1 := by dsimp only [P]; omega
  refine ⟨P,hT.le.trans (by exact_mod_cast hT'),?_,hR'⟩
  intro p hp
  exact Nat.mem_primesBelow.mpr
    ⟨((Nat.le_of_dvd hW (Nat.dvd_of_mem_primeFactors hp)).trans hW').trans_lt (Nat.lt_succ_self _),
      Nat.prime_of_mem_primeFactors hp⟩

end ActualTZOrdinaryReferenceCut318
