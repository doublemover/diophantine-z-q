module
public import ContactIntegerFractionField318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace ContactIntegerGenericLocalization318
open NumberField ContactFieldRamification318 ContactIntegerEtaleLocus318
  ContactIntegerEtaleCover318 ContactIntegerFractionField318
open scoped NumberField nonZeroDivisors
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

instance (u v : ℤ) : Algebra (BaseRing u v) ℚ := (baseToRational u v).toAlgebra

instance baseRationalTower (u v : ℤ) :
    @IsScalarTower ℤ (BaseRing u v) ℚ
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  exact Subsingleton.elim _ _

instance integerFieldTower (u v : ℤ) :
    @IsScalarTower ℤ (IntegerRing u v) (L u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  exact Subsingleton.elim _ _

/-- The rational generic point is the actual localization of the S-integer
base at the images of the nonzero rational integers. -/
instance rationalLocalization (u v : ℤ) :
    IsLocalization (Algebra.algebraMapSubmonoid (BaseRing u v) ℤ⁰) ℚ := by
  apply IsLocalization.isLocalization_of_submonoid_le (BaseRing u v) ℚ
    (Submonoid.powers (excludedProduct u v : ℤ)) ℤ⁰
  apply Submonoid.powers_le.mpr
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v))

/-- The same original contact field is obtained from the actual localized
integer cover by inverting the images of nonzero rational integers. -/
instance fieldLocalization (u v : ℤ) :
    IsLocalization (Algebra.algebraMapSubmonoid (IntegerRing u v) ℤ⁰) (L u v) := by
  let : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 (L u v)) ℤ⁰) (L u v) :=
    IsIntegralClosure.isLocalization ℤ ℚ (L u v) (𝓞 (L u v))
  have hle : Submonoid.powers (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ)) ≤
      Algebra.algebraMapSubmonoid (𝓞 (L u v)) ℤ⁰ := by
    apply Submonoid.powers_le.mpr
    refine ⟨(excludedProduct u v : ℤ), ?_, rfl⟩
    change (excludedProduct u v : ℤ) ∈ ℤ⁰
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v))
  have h := IsLocalization.isLocalization_of_submonoid_le
    (IntegerRing u v) (L u v) _ _ hle
  have he : (Algebra.algebraMapSubmonoid (𝓞 (L u v)) ℤ⁰).map
      (algebraMap (𝓞 (L u v)) (IntegerRing u v)) =
      Algebra.algebraMapSubmonoid (IntegerRing u v) ℤ⁰ := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, IsScalarTower.algebraMap_apply ℤ (𝓞 (L u v)) (IntegerRing u v) z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨algebraMap ℤ (𝓞 (L u v)) z, ⟨z, hz, rfl⟩,
        (IsScalarTower.algebraMap_apply ℤ (𝓞 (L u v)) (IntegerRing u v) z).symm⟩
  rw [he] at h
  exact h

/-- Both localizations use the very same denominator set through the actual
integer-cover map. -/
lemma denominator_image (u v : ℤ) :
    (Algebra.algebraMapSubmonoid (BaseRing u v) ℤ⁰).map (baseMap u v) =
      Algebra.algebraMapSubmonoid (IntegerRing u v) ℤ⁰ := by
  have h : (baseMap u v).comp (algebraMap ℤ (BaseRing u v)) =
      algebraMap ℤ (IntegerRing u v) := Subsingleton.elim _ _
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (RingHom.congr_fun h z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨algebraMap ℤ (BaseRing u v) z, ⟨z, hz, rfl⟩, RingHom.congr_fun h z⟩

end ContactIntegerGenericLocalization318
