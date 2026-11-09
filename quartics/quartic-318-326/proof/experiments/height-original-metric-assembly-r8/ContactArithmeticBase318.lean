module
public import ContactArithmeticDenominator318
public section
noncomputable section
namespace ContactArithmeticBase318
open ContactArithmeticDenominator318
open scoped nonZeroDivisors
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The actual explicitly chosen arithmetic base Z[1/denominator(c)]. -/
abbrev Base := Localization.Away (denominator c)
instance base_domain : IsDomain (Base c) := Localization.Away.isDomain (denominator_ne_zero c)
instance base_noetherian : IsNoetherianRing (Base c) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (denominator c)) (Base c) inferInstance
instance base_normal : IsIntegrallyClosed (Base c) := by
  apply isIntegrallyClosed_of_isLocalization (Base c) (Submonoid.powers (denominator c))
  exact powers_le_nonZeroDivisors_of_noZeroDivisors (denominator_ne_zero c)

/-- The original integer inclusion extends to the explicit base. -/
@[expose] def intoQ : Base c →+* ℚ :=
  IsLocalization.Away.lift (denominator c)
    (show IsUnit ((Int.castRingHom ℚ) (denominator c)) from
      isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (denominator_ne_zero c)))
@[simp] theorem intoQ_integer (z : ℤ) : intoQ c (algebraMap ℤ (Base c) z)=(z:ℚ) :=
  IsLocalization.Away.lift_eq _ _ z

instance rationalAlgebra : Algebra (Base c) ℚ := (intoQ c).toAlgebra
instance rationalTower : IsScalarTower ℤ (Base c) ℚ :=
  IsScalarTower.of_algebraMap_eq (fun z => (intoQ_integer c z).symm)

theorem intoQ_injective : Function.Injective (intoQ c) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (denominator c))]
  intro x y
  rw [intoQ_integer,intoQ_integer]
  exact (IsLocalization.injective (Base c)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (denominator_ne_zero c))).eq_iff.trans
      Int.cast_injective.eq_iff.symm

theorem algebraMap_injective : Function.Injective (algebraMap (Base c) ℚ) := intoQ_injective c

theorem denominator_unit : IsUnit (algebraMap ℤ (Base c) (denominator c)) :=
  IsLocalization.Away.algebraMap_isUnit (denominator c)

/-- Only explicitly inverted integer factors are used to obtain units. -/
theorem factor_unit (z : ℤ) (hz : z ∣ denominator c) :
    IsUnit (algebraMap ℤ (Base c) z) := by
  obtain ⟨w,hw⟩ := hz
  have h := denominator_unit c
  rw [hw,map_mul] at h
  exact isUnit_of_mul_isUnit_left h

theorem separation_unit :
    IsUnit (IntegralBranchDenominatorCover318.separationInteger:Base c) := by
  simpa only [map_intCast] using factor_unit c _ (separation_dvd c)
theorem two_unit : IsUnit (2:Base c) :=
  IntegralSmoothProperBicanonical318.two_unit (Base c) (separation_unit c)
end ContactArithmeticBase318
