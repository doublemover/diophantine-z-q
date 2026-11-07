module
public import Current326CoefficientBinding
public import Current326Bridge
public import Current326ExactDegree
public section

/-! The public interface for the literal stored 326-coordinate coefficient table.
The global arithmetic characterization is still an explicit hypothesis. -/
namespace Current326Final

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact length of the checked literal coefficient data. -/
theorem stored_term_count : Current326CoefficientBindingData.tableData.length = 3157 := by decide

/-- The literal table has coordinate degree exactly four. -/
theorem table_degree_exactly_four :
    Current326CoefficientBinding.tablePolynomial.totalDegree = 4 := by
  rw [Current326CoefficientBinding.table_eq_sos]
  exact Current326ExactDegree.degree_exactly_four

/-- The 325-witness table has precisely the same input projection as the
317-witness 318-coordinate polynomial. No arithmetic source theorem is assumed. -/
theorem table_zero_iff_318 (q : ℚ) :
    (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326CoefficientBinding.tablePolynomial = 0) ↔
    (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P = 0) := by
  rw [Current326CoefficientBinding.table_eq_sos]
  exact Current326Bridge.polynomial_zero_iff_318 q

/-- The literal table's zero set is equivalent to the original source system. -/
theorem table_zero_iff_source (q : ℚ) :
    (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326CoefficientBinding.tablePolynomial = 0) ↔
    CircuitReplay.HasSolution
      (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q := by
  rw [Current326CoefficientBinding.table_eq_sos]
  exact Current326Bridge.polynomial_zero_iff_source q

/-- Conditional arithmetic characterization, with its remaining premise visible. -/
theorem defines_integers_of_source_arithmetic
    (sourceArithmetic : ∀ q : ℚ,
      CircuitReplay.HasSolution
        (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q ↔
        ∃ z : ℤ, (z : ℚ) = q) :
    ∀ q : ℚ, (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326CoefficientBinding.tablePolynomial = 0) ↔
      ∃ z : ℤ, (z : ℚ) = q := by
  intro q
  exact (table_zero_iff_source q).trans (sourceArithmetic q)

end Current326Final
