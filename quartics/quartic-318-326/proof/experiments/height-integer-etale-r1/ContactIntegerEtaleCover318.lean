module
public import ContactIntegerEtaleLocus318
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public section
noncomputable section
namespace ContactIntegerEtaleCover318
open NumberField ContactRadical318 ContactFieldRamification318 ContactIntegerEtaleLocus318
open AlgebraicGeometry CategoryTheory
open scoped NumberField
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

abbrev BaseRing (u v : ℤ) := Localization.Away (excludedProduct u v : ℤ)
abbrev IntegerRing (u v : ℤ) :=
  Localization.Away (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ))

/-- The actual localized integer inclusion, with the same excluded product
on the original rational base and the original ring of integers. -/
@[expose] def baseMap (u v : ℤ) : BaseRing u v →+* IntegerRing u v :=
  Localization.awayMap (algebraMap ℤ (𝓞 (L u v))) (excludedProduct u v : ℤ)

instance (u v : ℤ) : Algebra (BaseRing u v) (IntegerRing u v) := (baseMap u v).toAlgebra
instance integerBaseTower (u v : ℤ) :
    @IsScalarTower ℤ (BaseRing u v) (IntegerRing u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  exact Subsingleton.elim _ _

lemma baseMap_injective (u v : ℤ) : Function.Injective (baseMap u v) := by
  apply Localization.awayMap_injective_iff.mpr
  intro a ha
  have hz : a = 0 := by
    apply (FaithfulSMul.algebraMap_injective ℤ (𝓞 (L u v)))
    simpa only [map_zero] using ha
  exact ⟨0, by simp [hz]⟩

instance (u v : ℤ) : FaithfulSMul (BaseRing u v) (IntegerRing u v) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (baseMap_injective u v)

instance (u v : ℤ) : IsDomain (IntegerRing u v) :=
  Localization.Away.isDomain (by
    rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 (L u v)))]
    exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v)))

instance integerRing_finite (u v : ℤ) : Module.Finite (BaseRing u v) (IntegerRing u v) := by
  let : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 (L u v))
      (Submonoid.powers (excludedProduct u v : ℤ))) (IntegerRing u v) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  exact Module.Finite.of_isLocalization ℤ (𝓞 (L u v)) (Submonoid.powers (excludedProduct u v : ℤ))

/-- The actual localization is finite etale over the actual S-integer base. -/
theorem finite_etale (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) :
    Module.Finite (BaseRing u v) (IntegerRing u v) ∧
      Algebra.Etale (BaseRing u v) (IntegerRing u v) := by
  let : Algebra.Etale ℤ (BaseRing u v) := Algebra.Etale.of_isLocalizationAway (excludedProduct u v : ℤ)
  let : Algebra.Etale ℤ (IntegerRing u v) := integerLocalization_etale u v hn
  exact ⟨inferInstance, Algebra.Etale.of_restrictScalars ℤ (BaseRing u v) (IntegerRing u v)⟩

/-- The actual affine morphism of the localized integer rings. -/
@[expose] def coverMap (u v : ℤ) :
    Spec (CommRingCat.of (IntegerRing u v)) ⟶ Spec (CommRingCat.of (BaseRing u v)) :=
  Spec.map (CommRingCat.ofHom (baseMap u v))

instance coverMap_finite (u v : ℤ) : IsFinite (coverMap u v) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- This is an actual finite etale surjective cover of the S-integer base,
not only a pointwise statement about ramification indices. -/
theorem cover_properties (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) :
    IsFinite (coverMap u v) ∧ Etale (coverMap u v) ∧ Surjective (coverMap u v) := by
  let : Algebra.Etale (BaseRing u v) (IntegerRing u v) := (finite_etale u v hn).2
  have he : Etale (coverMap u v) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hs : Flat (coverMap u v) ∧ Surjective (coverMap u v) := by
    apply (flat_and_surjective_SpecMap_iff _).mpr
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact ⟨inferInstance, he, hs.2⟩

/-- The same exact integer-ring map supplies an fppf cover. -/
theorem fppf_cover (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) :
    Presieve.singleton (coverMap u v) ∈
      Scheme.fppfPrecoverage (Spec (CommRingCat.of (BaseRing u v))) := by
  let : Etale (coverMap u v) := (cover_properties u v hn).2.1
  let : Surjective (coverMap u v) := (cover_properties u v hn).2.2
  exact (coverMap u v).singleton_mem_fppfPrecoverage

end ContactIntegerEtaleCover318
