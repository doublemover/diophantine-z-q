module
public import VerticalSection318
public section
noncomputable section
namespace AlgebraicSectionPullback318
open VerticalSection318
set_option maxHeartbeats 0

@[expose] def branchDen {S : Type*} [CommRing S] (i : Fin 4) (z : S) : S :=
  ∏ j : {j : Fin 4 // j ≠ i}, ((contacts i : S) - (contacts j : S) + z^2)
@[expose] def infinityDen {S : Type*} [CommRing S] (z : S) : S :=
  ∏ j : Fin 4, (1 - (contacts j : S)*z^2)

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
@[expose] def coefficient0 (D : Derivation R K K) (t : K) : K :=
  (D t)^2 / denominator t
@[expose] def coefficient1 (D : Derivation R K K) (t : K) : K :=
  t * coefficient0 D t

theorem finite_polynomial (i : Fin 4) (z : K) :
    denominator ((contacts i : K) + z^2) = z^2 * branchDen i z := by
  classical
  unfold denominator branchDen
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [add_sub_cancel_left]
  rw [mul_comm]
  congr 1
  simp_rw [show ∀ j : Fin 4, (contacts i : K) + z^2 - contacts j =
    (contacts i : K) - contacts j + z^2 by intro j; ring]
  exact Finset.prod_subtype (Finset.univ.erase i) (by simp) _

theorem infinity_polynomial (z : K) (hz : z ≠ 0) :
    denominator (1 / z^2) = infinityDen z / (z^2)^4 := by
  unfold denominator infinityDen
  have he (j : Fin 4) : (1 : K) / z^2 - contacts j =
      (1 - (contacts j : K)*z^2) / z^2 := by field_simp
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp

theorem finite_derivative (D : Derivation R K K) (i : Fin 4) (z : K) :
    D ((contacts i : K) + z^2) = 2*z*D z := by
  rw [D.map_add, D.map_intCast, zero_add, D.leibniz_pow]
  simp [smul_eq_mul, nsmul_eq_mul, mul_assoc]

theorem infinity_derivative (D : Derivation R K K) (z : K) (hz : z ≠ 0) :
    D (1 / z^2) = -2 * D z / z^3 := by
  rw [D.leibniz_div, D.map_one_eq_zero, D.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- Actual relative differentiation and cancellation of the branch square. -/
theorem finite_coefficient0 (D : Derivation R K K) (i : Fin 4) (z : K) (hz : z ≠ 0) :
    coefficient0 D ((contacts i : K) + z^2) = 4*(D z)^2 / branchDen i z := by
  rw [coefficient0, finite_derivative, finite_polynomial]
  by_cases hd : branchDen i z = 0
  · simp [hd]
  · field_simp
    ring

theorem finite_coefficient1 (D : Derivation R K K) (i : Fin 4) (z : K) (hz : z ≠ 0) :
    coefficient1 D ((contacts i : K) + z^2) =
      ((contacts i : K) + z^2) * (4*(D z)^2 / branchDen i z) := by
  rw [coefficient1, finite_coefficient0 D i z hz]

/-- The actual rational-function infinity pullback, including its z-squared
zero in the first coefficient and its cancellation in the second. -/
theorem infinity_coefficient0 (D : Derivation R K K) (z : K) (hz : z ≠ 0) :
    coefficient0 D (1/z^2) = 4*z^2*(D z)^2 / infinityDen z := by
  rw [coefficient0, infinity_derivative D z hz, infinity_polynomial z hz]
  by_cases hd : infinityDen z = 0
  · simp [hd]
  · field_simp
    ring

theorem infinity_coefficient1 (D : Derivation R K K) (z : K) (hz : z ≠ 0) :
    coefficient1 D (1/z^2) = 4*(D z)^2 / infinityDen z := by
  rw [coefficient1, infinity_coefficient0 D z hz]
  by_cases hd : infinityDen z = 0
  · simp [hd]
  · field_simp

/-- In the actual dz frame these are exactly the source's regular coefficients. -/
theorem finite_coordinate_coefficients (D : Derivation R K K) (i : Fin 4) (z : K)
    (hz : z ≠ 0) (hDz : D z = 1) :
    coefficient0 D ((contacts i : K) + z^2) = 4 / branchDen i z ∧
    coefficient1 D ((contacts i : K) + z^2) =
      ((contacts i : K) + z^2) * (4 / branchDen i z) := by
  simp [finite_coefficient0 D i z hz, finite_coefficient1 D i z hz, hDz]

theorem infinity_coordinate_coefficients (D : Derivation R K K) (z : K)
    (hz : z ≠ 0) (hDz : D z = 1) :
    coefficient0 D (1/z^2) = 4*z^2 / infinityDen z ∧
    coefficient1 D (1/z^2) = 4 / infinityDen z := by
  rw [infinity_coefficient0 D z hz, infinity_coefficient1 D z hz, hDz]
  simp

end AlgebraicSectionPullback318
