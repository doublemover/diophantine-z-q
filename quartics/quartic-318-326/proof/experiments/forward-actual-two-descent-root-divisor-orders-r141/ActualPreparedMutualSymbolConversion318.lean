module
public import ActualTwoDescentUnitSquareNecessity318
public import ActualTwoDescentMutualSymbolRows318
public section
noncomputable section
namespace ActualPreparedMutualSymbolConversion318
open ActualTwoDescentUnitSquareNecessity318 ActualTwoDescentMutualSymbolRows318
open scoped BigOperators

/-- Reverse direction to the existing mutual-symbol-to-local-roots theorem.
Both directed actual square roots of the WHOLE products are retained. No
individual cross-prime symbol is asserted and no reciprocity substitution is used. -/
theorem mutual_symbols_of_actual_roots {B J : Type*} [Fintype B] [Fintype J]
    (qB : B → ℕ) (qJ : J → ℕ)
    [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hdis : ∀ b j, qB b≠qJ j)
    (hTheta : ∀ b, ∃ r : ℚ_[qB b], r^2=((∏ j, qJ j : ℕ) : ℚ_[qB b]))
    (hBeta : ∀ j, ∃ r : ℚ_[qJ j], r^2=((∏ b, qB b : ℕ) : ℚ_[qJ j])) :
    MutualSymbols qB qJ := by
  constructor
  · intro b
    have hc : Nat.Coprime (∏ j, qJ j) (qB b) := by
      apply Nat.coprime_prod_left_iff.mpr
      intro j _
      exact (Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm (hdis b j))
    have hcZ : IsCoprime ((∏ j, qJ j : ℕ) : ℤ) (qB b : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa only [Int.gcd_natCast_natCast] using hc
    obtain ⟨r,hr⟩ := hTheta b
    apply actual_unit_square_symbol ((∏ j, qJ j : ℕ) : ℤ) hcZ r
    simpa only [Int.cast_natCast] using hr
  · intro j
    have hc : Nat.Coprime (∏ b, qB b) (qJ j) := by
      apply Nat.coprime_prod_left_iff.mpr
      intro b _
      exact (Nat.coprime_primes Fact.out Fact.out).mpr (hdis b j)
    have hcZ : IsCoprime ((∏ b, qB b : ℕ) : ℤ) (qJ j : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa only [Int.gcd_natCast_natCast] using hc
    obtain ⟨r,hr⟩ := hBeta j
    apply actual_unit_square_symbol ((∏ b, qB b : ℕ) : ℤ) hcZ r
    simpa only [Int.cast_natCast] using hr

/-- Literal factorization preserves the same beta/theta coefficients when
passing from their support-wise local square roots to the finite descent API. -/
theorem mutual_symbols_of_coefficient_roots {B J : Type*} [Fintype B] [Fintype J]
    (beta theta : ℕ) (qB : B → ℕ) (qJ : J → ℕ)
    [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hBetaFactor : (∏ b, qB b)=beta) (hThetaFactor : (∏ j, qJ j)=theta)
    (hdis : ∀ b j, qB b≠qJ j)
    (hTheta : ∀ (p : ℕ) [Fact p.Prime], p∣beta →
      ∃ r : ℚ_[p], r^2=(theta:ℚ_[p]))
    (hBeta : ∀ (p : ℕ) [Fact p.Prime], p∣theta →
      ∃ r : ℚ_[p], r^2=(beta:ℚ_[p])) : MutualSymbols qB qJ := by
  apply mutual_symbols_of_actual_roots qB qJ hdis
  · intro b
    have hd : qB b∣beta := by
      rw [←hBetaFactor]
      exact Finset.dvd_prod_of_mem qB (Finset.mem_univ b)
    obtain ⟨r,hr⟩ := hTheta (qB b) hd
    exact ⟨r,by simpa only [hThetaFactor] using hr⟩
  · intro j
    have hd : qJ j∣theta := by
      rw [←hThetaFactor]
      exact Finset.dvd_prod_of_mem qJ (Finset.mem_univ j)
    obtain ⟨r,hr⟩ := hBeta (qJ j) hd
    exact ⟨r,by simpa only [hBetaFactor] using hr⟩

end ActualPreparedMutualSymbolConversion318
