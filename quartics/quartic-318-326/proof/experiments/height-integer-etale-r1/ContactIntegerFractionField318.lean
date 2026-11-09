module
public import ContactIntegerEtaleCover318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace ContactIntegerFractionField318
open NumberField ContactFieldRamification318 ContactIntegerEtaleLocus318 ContactIntegerEtaleCover318
open scoped NumberField
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

lemma excluded_image_unit (u v : ℤ) :
    IsUnit (algebraMap (𝓞 (L u v)) (L u v)
      (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ))) := by
  rw [← IsScalarTower.algebraMap_apply]
  apply isUnit_iff_ne_zero.mpr
  change (excludedProduct u v : L u v) ≠ 0
  exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v))

/-- The actual localization embeds into the original chosen contact field
by the universal map extending its original integer-ring inclusion. -/
@[expose] def integerToField (u v : ℤ) : IntegerRing u v →+* L u v :=
  IsLocalization.Away.lift
    (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ)) (excluded_image_unit u v)

lemma integerToField_original (u v : ℤ) (x : 𝓞 (L u v)) :
    integerToField u v (algebraMap (𝓞 (L u v)) (IntegerRing u v) x) =
      algebraMap (𝓞 (L u v)) (L u v) x :=
  IsLocalization.Away.lift_eq _ _ _

instance (u v : ℤ) : Algebra (IntegerRing u v) (L u v) := (integerToField u v).toAlgebra

instance integerTower (u v : ℤ) : IsScalarTower (𝓞 (L u v)) (IntegerRing u v) (L u v) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (IsLocalization.Away.lift_comp _ (excluded_image_unit u v)).symm

/-- The fraction field of the actual S-integer cover is the exact original
contact field, not a separately selected isomorphic number field. -/
instance originalFractionField (u v : ℤ) : IsFractionRing (IntegerRing u v) (L u v) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ)))
    (IntegerRing u v) (L u v)

lemma integerToField_injective (u v : ℤ) : Function.Injective (integerToField u v) :=
  IsFractionRing.injective (IntegerRing u v) (L u v)

/-- The S-integer base maps into the unchanged rational base. -/
@[expose] def baseToRational (u v : ℤ) : BaseRing u v →+* ℚ :=
  IsLocalization.Away.lift (excludedProduct u v : ℤ)
    (show IsUnit (algebraMap ℤ ℚ (excludedProduct u v : ℤ)) from
      isUnit_iff_ne_zero.mpr (by
        change (excludedProduct u v : ℚ) ≠ 0
        exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v))))

/-- The entire localization square uses the same original Q-algebra map
into the same original contact field. -/
theorem field_square (u v : ℤ) :
    (integerToField u v).comp (baseMap u v) =
      (algebraMap ℚ (L u v)).comp (baseToRational u v) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (excludedProduct u v : ℤ))
  exact Subsingleton.elim _ _

end ContactIntegerFractionField318
