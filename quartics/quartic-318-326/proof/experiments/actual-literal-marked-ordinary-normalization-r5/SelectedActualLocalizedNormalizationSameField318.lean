module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

public section
noncomputable section

namespace SelectedActualLocalizedNormalizationSameField318

variable {R A B O F : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing O]
  [Field F] [Algebra R A] [Algebra R B] [Algebra R O] [Algebra R F]
  [Algebra A O] [Algebra B O] [Algebra A F] [Algebra B F] [Algebra O F]
  [IsScalarTower R A O] [IsScalarTower R B O] [IsScalarTower R A F]
  [IsScalarTower R B F] [IsScalarTower A O F] [IsScalarTower B O F]
  [IsIntegralClosure B R F] [Algebra.IsIntegral R B]

/-- Localize the already matched normal order, using exactly the
same embedding in the actual whole marked field. The missing
integral-closure instance is constructed by clearing the denominator
of a monic equation, rather than by assuming another normal chart. -/
theorem normalization_localizes_in_same_field (M : Submonoid R)
    [IsLocalization M A] [IsLocalization (Algebra.algebraMapSubmonoid B M) O] :
    IsIntegralClosure O A F := by
  have hiB : Function.Injective (algebraMap B F) := IsIntegralClosure.algebraMap_injective B R F
  constructor
  · apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Algebra.algebraMapSubmonoid B M) (algebraMap O F)).2
    intro a b
    constructor
    · exact congrArg (algebraMap O F)
    · intro h
      apply congrArg (algebraMap B O)
      apply hiB
      simpa only [← IsScalarTower.algebraMap_apply B O F] using h
  · intro x
    constructor
    · intro hx
      obtain ⟨m,hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) M x hx
      obtain ⟨b,hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B) (R := R) (B := F)).mp hm
      have hB : algebraMap B F b = algebraMap R F (m : R) * x := by
        simpa only [Submonoid.smul_def,Algebra.smul_def] using hb
      let u := (IsLocalization.map_units A m).unit
      let v : A := ↑u⁻¹
      have hinv : v * algebraMap R A (m : R) = 1 :=
        (congrArg (fun a : A => v * a) (IsLocalization.map_units A m).unit_spec.symm).trans
          (Units.inv_mul u)
      have hinvF : algebraMap A F v * algebraMap R F (m : R) = 1 := by
        rw [IsScalarTower.algebraMap_apply R A F,← map_mul,hinv,map_one]
      refine ⟨algebraMap A O v * algebraMap B O b,?_⟩
      calc
        algebraMap O F (algebraMap A O v * algebraMap B O b) =
            algebraMap A F v * algebraMap B F b := by
          rw [map_mul,← IsScalarTower.algebraMap_apply A O F,
            ← IsScalarTower.algebraMap_apply B O F]
        _ = x := by rw [hB,← mul_assoc,hinvF,one_mul]
    · rintro ⟨b,rfl⟩
      have hmap := IsLocalization.algebraMap_eq_map_map_submonoid
        (S := B) (Rₘ := A) (Sₘ := O) M
      have hInt : IsIntegral A b := by
        change (algebraMap A O).IsIntegralElem b
        rw [hmap]
        exact isIntegral_localization (Rₘ := A) (Sₘ := O) (M := M) b
      exact hInt.map (IsScalarTower.toAlgHom A O F)

/-- An independently constructed ordinary ring, if it is already
verified as the whole integral closure in that same field, receives
the one canonical normalization comparison with its generic map fixed. -/
theorem comparison_preserves_the_whole_field {C : Type*} [CommRing C]
    [Algebra A C] [Algebra C F] [IsScalarTower A C F]
    [IsIntegralClosure C A F] (M : Submonoid R) [IsLocalization M A]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) O] :
    ∃ e : C ≃ₐ[A] O, ∀ x : C, algebraMap O F (e x) = algebraMap C F x := by
  letI : IsIntegralClosure O A F := normalization_localizes_in_same_field (B := B) M
  exact ⟨IsIntegralClosure.equiv A C F O,IsIntegralClosure.algebraMap_equiv A C F O⟩

end SelectedActualLocalizedNormalizationSameField318

#print axioms SelectedActualLocalizedNormalizationSameField318.normalization_localizes_in_same_field
#print axioms SelectedActualLocalizedNormalizationSameField318.comparison_preserves_the_whole_field
