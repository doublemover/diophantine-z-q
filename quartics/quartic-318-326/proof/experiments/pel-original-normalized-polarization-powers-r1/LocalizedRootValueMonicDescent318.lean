module
public import MonicGrowthIntegralFraction318
public import WeightedRootProductBound318
public section
noncomputable section
namespace LocalizedRootValueMonicDescent318
open Polynomial ComplexPolynomialOpenPoints318
abbrev Base := MvPolynomial (Fin 2) ℂ

/-- Every root is counted with its actual multiplicity. A polynomial
bound on ALL root values gives denominator-free growth of every
coefficient; no simple-root or distinct-value hypothesis is used. -/
theorem coefficient_bound (d : Base) (Q : Polynomial (Localization.Away d))
    (m N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hroots : ∀ v (hv : MvPolynomial.eval v d ≠ 0), ∃ r : Fin m → ℂ,
      Q.map (evaluation d v hv) = ∏ i : Fin m, (X-Polynomial.C (r i)) ∧
      ∀ i, ‖r i‖ ≤ C*(1+‖v‖)^N)
    (n : ℕ) (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    ‖evaluation d v hv (Q.coeff n)‖ ≤ (1+C)^m * (1+‖v‖)^(N*m) := by
  classical
  obtain ⟨r,hr,hb⟩ := hroots v hv
  have hx : 1 ≤ (1+‖v‖)^N := one_le_pow₀ (by linarith [norm_nonneg v])
  have hbase : 1+C*(1+‖v‖)^N ≤ (1+C)*(1+‖v‖)^N := by nlinarith
  have hcoeff := WeightedRootProductBound318.coeff_bound Finset.univ r 1
    (1+C*(1+‖v‖)^N) (by norm_num) (by positivity)
    (fun i _ => by simpa only [one_mul] using add_le_add_left (hb i) 1) n
  have he : ‖evaluation d v hv (Q.coeff n)‖ =
      ‖(∏ i : Fin m, (X-Polynomial.C (r i))).coeff n‖ := by
    rw [←hr,Polynomial.coeff_map]
  rw [he]
  calc
    ‖(∏ i : Fin m, (X-Polynomial.C (r i))).coeff n‖ ≤ (1+C*(1+‖v‖)^N)^m := by
      simpa only [Finset.card_univ,Fintype.card_fin,one_pow,one_mul] using hcoeff
    _ ≤ ((1+C)*(1+‖v‖)^N)^m := pow_le_pow_left₀ (by positivity) hbase m
    _ = (1+C)^m * (1+‖v‖)^(N*m) := by rw [mul_pow,←pow_mul]

/-- Literal all-root products with polynomially bounded values descend
to a monic equation over the original two-dimensional polynomial base. -/
theorem exists_monic (d : Base) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (m N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hroots : ∀ v (hv : MvPolynomial.eval v d ≠ 0), ∃ r : Fin m → ℂ,
      Q.map (evaluation d v hv) = ∏ i : Fin m, (X-Polynomial.C (r i)) ∧
      ∀ i, ‖r i‖ ≤ C*(1+‖v‖)^N) :
    ∃ P : Polynomial Base, P.Monic ∧
      P.map (algebraMap Base (Localization.Away d)) = Q := by
  apply LocalizedMonicPolynomialDescent318.exists_monic d hd Q hm
  intro n
  exact ⟨N*m,(1+C)^m,by positivity,
    fun v hv => coefficient_bound d Q m N C hC hroots n v hv⟩
end LocalizedRootValueMonicDescent318
