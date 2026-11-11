module
public import LocalizedSelectedCoefficientBound318
public import LocalizedPolynomialCommonNumerators318
public import MvPolynomialEvaluationGrowth318
public section
noncomputable section
namespace LocalizedSelectedPolynomialGrowth318
open Polynomial
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318
variable {ι : Type*} [Fintype ι]

/-- Actual uniform pole and polynomial-growth bound for ALL coefficients
of the canonical selected factor. The same original d clears poles;
constants and exponents are independent of coefficient index and point.
The subset may have varying degree and need not yet be proved connected. -/
theorem exists_selected_growth (d : MvPolynomial ι ℂ)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : ι → ℂ, MvPolynomial.eval v d ≠ 0 → ∀ n : ℕ,
        ‖MvPolynomial.eval v d ^ M * (selectedPolynomial d Q hm S v).coeff n‖ ≤
          C*(1+‖v‖)^N := by
  obtain ⟨M,b,hb⟩ := LocalizedPolynomialCommonNumerators318.exists_common_numerators d Q
  obtain ⟨C,hC,N,hnum⟩ := MvPolynomialEvaluationGrowth318.exists_uniform_growth
    (Finset.range Q.natDegree) b
  obtain ⟨D,hD,K,hd⟩ := MvPolynomialEvaluationGrowth318.exists_growth d
  let L := N+K*M
  let E := C+3*D^M
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨M*Q.natDegree,L*Q.natDegree,E^Q.natDegree,pow_nonneg hE _,?_⟩
  intro v hv n
  let δ := ‖MvPolynomial.eval v d‖^M
  let A := C*(1+‖v‖)^N
  have hδ : 0 < δ := pow_pos (norm_pos_iff.mpr hv) _
  have hA : 0 ≤ A := mul_nonneg hC (pow_nonneg (by positivity) _)
  have hc : ∀ k < Q.natDegree, δ *
      ‖LocalizedComplexCoefficientAnalytic318.value d (Q.coeff k) v‖ ≤ A := by
    intro k hk
    have hh := congrArg norm (hb k hk v hv)
    rw [norm_mul,norm_pow] at hh
    change δ * ‖LocalizedComplexCoefficientAnalytic318.value d (Q.coeff k) v‖ = _ at hh
    rw [hh]
    exact hnum k (Finset.mem_range.mpr hk) v
  have hδg : δ ≤ D^M*(1+‖v‖)^(K*M) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hd v) M
    simpa only [mul_pow,←pow_mul] using hh
  have h1 : 1 ≤ 1+‖v‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hNg : (1+‖v‖)^N ≤ (1+‖v‖)^L := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
  have hKg : (1+‖v‖)^(K*M) ≤ (1+‖v‖)^L := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
  have hlarge : A+3*δ ≤ E*(1+‖v‖)^L := by
    calc
      A+3*δ ≤ C*(1+‖v‖)^L + 3*(D^M*(1+‖v‖)^L) :=
        add_le_add (mul_le_mul_of_nonneg_left hNg hC)
          (mul_le_mul_of_nonneg_left (hδg.trans
            (mul_le_mul_of_nonneg_left hKg (pow_nonneg hD _))) (by norm_num))
      _ = E*(1+‖v‖)^L := by dsimp [E]; ring
  have hbound := LocalizedSelectedCoefficientBound318.selected_coefficient_bound
    d Q hm hs S v hv δ A hδ hA hc n
  calc
    ‖MvPolynomial.eval v d ^ (M*Q.natDegree) * (selectedPolynomial d Q hm S v).coeff n‖ =
        δ^Q.natDegree * ‖(selectedPolynomial d Q hm S v).coeff n‖ := by
          rw [norm_mul,norm_pow,pow_mul]
    _ ≤ (A+3*δ)^Q.natDegree := hbound
    _ ≤ (E*(1+‖v‖)^L)^Q.natDegree :=
      pow_le_pow_left₀ (by positivity) hlarge _
    _ = E^Q.natDegree*(1+‖v‖)^(L*Q.natDegree) := by rw [mul_pow,←pow_mul]
end LocalizedSelectedPolynomialGrowth318
