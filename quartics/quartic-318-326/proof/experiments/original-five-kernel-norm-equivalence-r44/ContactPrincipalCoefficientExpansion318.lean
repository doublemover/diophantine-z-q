module
public import ContactWholePrincipalReduction318
public import Mathlib.Algebra.Polynomial.Degree.Support

public section
noncomputable section
namespace ContactPrincipalCoefficientExpansion318
open Polynomial ContactInfinityRegularFractions318
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The literal original infinity polynomial map into the overlap ring. -/
@[expose] def polynomialMap : ℚ[X] →+* OverlapRing c :=
  (InfinityOverlapLocalization318.toOpen c).comp
    ((algebraMap (Base c) (InfinityRing c)).comp (algebraMap ℚ[X] (Base c)))

theorem polynomialMap_C (q : ℚ) :
    polynomialMap c (C q) = algebraMap ℚ (OverlapRing c) q :=
  RingHom.map_rat_algebraMap (polynomialMap c) q

theorem polynomialMap_X : polynomialMap c X = SourceInfinityOverlap318.u c := rfl

/-- All polynomial coefficients are expanded in the original overlap ring. -/
theorem polynomialMap_expansion (P : ℚ[X]) :
    polynomialMap c P = ∑ j ∈ P.support,
      algebraMap ℚ (OverlapRing c) (P.coeff j) * (SourceInfinityOverlap318.u c)^j := by
  have hP : (∑ j ∈ P.support, C (P.coeff j) * X^j) = P := sum_C_mul_X_pow_eq P
  calc
    polynomialMap c P = polynomialMap c (∑ j ∈ P.support, C (P.coeff j) * X^j) :=
      congrArg (polynomialMap c) hP.symm
    _ = _ := by simp only [map_sum,map_mul,map_pow,polynomialMap_C,polynomialMap_X]

/-- Cancel a numerator power against the actual overlap inverse without
passing to a different field or introducing a new localization. -/
theorem coordinate_pole_cancel (j n : ℕ) (hjn : j ≤ n) :
    (SourceInfinityOverlap318.u c)^j * (inverseU c)^n = (inverseU c)^(n-j) := by
  have he : n = j + (n-j) := by omega
  calc
    (SourceInfinityOverlap318.u c)^j * (inverseU c)^n =
        (SourceInfinityOverlap318.u c)^j * ((inverseU c)^j * (inverseU c)^(n-j)) := by
      conv_lhs => rw [he,pow_add]
    _ = ((SourceInfinityOverlap318.u c) * inverseU c)^j * (inverseU c)^(n-j) := by
      rw [mul_pow]
      ring
    _ = (inverseU c)^(n-j) := by rw [ContactWholePrincipalReduction318.u_inverse,one_pow,one_mul]

theorem support_lt_pole (P : ℚ[X]) (n : ℕ) (hP : P.degree < (n : WithBot ℕ))
    (j : ℕ) (hj : j ∈ P.support) : j < n := by
  exact_mod_cast lt_of_le_of_lt (le_degree_of_mem_supp j hj) hP

/-- The actual principal term is the complete finite sum of its weighted
negative-power coefficients. The empty/zero-polynomial case is included. -/
theorem principalTerm_expansion (P : ℚ[X]) (n : ℕ) (hP : P.degree < (n : WithBot ℕ)) :
    principalTerm c P n = ∑ j ∈ P.support,
      algebraMap ℚ (OverlapRing c) (P.coeff j) * (inverseU c)^(n-j) := by
  change polynomialMap c P * (inverseU c)^n = _
  rw [polynomialMap_expansion,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc,coordinate_pole_cancel c j n (Nat.le_of_lt (support_lt_pole P n hP j hj))]

end ContactPrincipalCoefficientExpansion318
