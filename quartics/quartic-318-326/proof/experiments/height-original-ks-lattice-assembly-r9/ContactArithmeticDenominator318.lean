module
public import IntegralPencilLineComparison318
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace ContactArithmeticDenominator318
set_option maxHeartbeats 800000
variable (c : Fin 4 → ℚˣ)

/-- A concrete finite denominator for the original four rational twists and
all original good-model exclusions. Signs of twist numerators are retained. -/
@[expose] def denominator : ℤ :=
  IntegralBranchDenominatorCover318.separationInteger *
    ∏ i : Fin 4, ((c i : ℚ).num * ((c i : ℚ).den : ℤ))

theorem denominator_ne_zero : denominator c ≠ 0 := by
  apply mul_ne_zero
  · norm_num [IntegralBranchDenominatorCover318.separationInteger]
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact mul_ne_zero (Rat.num_ne_zero.mpr (c i).ne_zero)
      (Int.natCast_ne_zero.mpr (c i : ℚ).den_nz)

theorem separation_dvd : IntegralBranchDenominatorCover318.separationInteger ∣ denominator c :=
  dvd_mul_right _ _

theorem factor_dvd (i : Fin 4) :
    (c i : ℚ).num * ((c i : ℚ).den : ℤ) ∣ denominator c := by
  exact (Finset.dvd_prod_of_mem (fun j : Fin 4 =>
    (c j : ℚ).num * ((c j : ℚ).den : ℤ)) (Finset.mem_univ i)).trans (dvd_mul_left _ _)

theorem numerator_dvd (i : Fin 4) : (c i : ℚ).num ∣ denominator c :=
  (dvd_mul_right _ _).trans (factor_dvd c i)
theorem denominator_dvd (i : Fin 4) : ((c i : ℚ).den : ℤ) ∣ denominator c :=
  (dvd_mul_left _ _).trans (factor_dvd c i)
end ContactArithmeticDenominator318
