module
public import LocalizedComplexCoefficientAnalytic318
public import Mathlib.Tactic
public section
noncomputable section
namespace LocalizedPolynomialCommonNumerators318
open Polynomial
variable {ι : Type*} [Fintype ι]

/-- One power of the SAME original base denominator clears every
coefficient below the fixed polynomial degree simultaneously. No change
of base open, fraction field replacement or selected-factor premise. -/
theorem exists_common_numerators (d : MvPolynomial ι ℂ)
    (Q : Polynomial (Localization.Away d)) :
    ∃ M : ℕ, ∃ b : ℕ → MvPolynomial ι ℂ,
      ∀ k < Q.natDegree, ∀ v : ι → ℂ, MvPolynomial.eval v d ≠ 0 →
        MvPolynomial.eval v d ^ M *
          LocalizedComplexCoefficientAnalytic318.value d (Q.coeff k) v =
            MvPolynomial.eval v (b k) := by
  classical
  choose a n h using fun k : ℕ =>
    LocalizedComplexCoefficientAnalytic318.exists_ratio d (Q.coeff k)
  let M := (Finset.range Q.natDegree).sup n
  refine ⟨M,fun k => a k * d^(M-n k),?_⟩
  intro k hk v hv
  have hn : n k ≤ M := Finset.le_sup (f := n) (Finset.mem_range.mpr hk)
  rw [h k v hv,MvPolynomial.eval_mul,MvPolynomial.eval_pow,←mul_div_assoc]
  apply (div_eq_iff (pow_ne_zero (n k) hv)).mpr
  calc
    MvPolynomial.eval v d ^ M * MvPolynomial.eval v (a k) =
      MvPolynomial.eval v (a k) *
        (MvPolynomial.eval v d ^ (M-n k) * MvPolynomial.eval v d ^ n k) := by
          rw [←pow_add,Nat.sub_add_cancel hn]
          ring
    _ = _ := by ring
end LocalizedPolynomialCommonNumerators318
