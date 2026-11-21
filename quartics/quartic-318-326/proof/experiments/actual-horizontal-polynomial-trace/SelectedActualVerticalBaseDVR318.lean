module
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public section
noncomputable section

open Polynomial

namespace SelectedActualVerticalBaseDVR318

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The literal generic point of the arithmetic vertical fiber,
as the kernel of coefficientwise residue. -/
@[expose] def verticalPrime : Ideal O[X] :=
  RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue O))

instance vertical_prime : (verticalPrime O).IsPrime :=
  RingHom.ker_isPrime (Polynomial.mapRingHom (IsLocalRing.residue O))

abbrev verticalDVR := Localization.AtPrime (verticalPrime O)
abbrev commonField := FractionRing O[X]

/-- The field does not depend on the vertical prime. -/
theorem same_fraction_field : IsFractionRing (verticalDVR O) (commonField O) :=
  inferInstance

theorem into_common_field : Function.Injective (algebraMap (verticalDVR O) (commonField O)) :=
  IsFractionRing.injective (verticalDVR O) (commonField O)

theorem prime_eq_span (π : O) (hπ : Irreducible π) :
    verticalPrime O = Ideal.span ({C π} : Set O[X]) := by
  unfold verticalPrime
  rw [Polynomial.ker_mapRingHom, IsLocalRing.ker_residue, hπ.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]

theorem localized_maximalIdeal (π : O) (hπ : Irreducible π) :
    IsLocalRing.maximalIdeal (verticalDVR O) =
      Ideal.span ({algebraMap O[X] (verticalDVR O) (C π)} : Set (verticalDVR O)) := by
  calc
    IsLocalRing.maximalIdeal (verticalDVR O) =
        (verticalPrime O).map (algebraMap O[X] (verticalDVR O)) :=
      Localization.AtPrime.map_eq_maximalIdeal.symm
    _ = _ := by
      rw [prime_eq_span O π hπ, Ideal.map_span, Set.image_singleton]

theorem uniformizer_ne_zero (π : O) (hπ : Irreducible π) :
    algebraMap O[X] (verticalDVR O) (C π) ≠ 0 := by
  have hi : Function.Injective (algebraMap O[X] (verticalDVR O)) :=
    IsLocalization.injective (verticalDVR O) (verticalPrime O).primeCompl_le_nonZeroDivisors
  exact fun h => hπ.ne_zero (Polynomial.C_injective (hi (h.trans (map_zero _).symm)))

theorem vertical_uniformizer (π : O) (hπ : Irreducible π) :
    Irreducible (algebraMap O[X] (verticalDVR O) (C π)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (uniformizer_ne_zero O π hπ) (localized_maximalIdeal O π hπ)

/-- The actual localized polynomial ring is a DVR, including in
residue characteristics two and three. -/
instance vertical_isDVR : IsDiscreteValuationRing (verticalDVR O) := by
  letI : IsNoetherianRing (verticalDVR O) :=
    IsLocalization.isNoetherianRing (verticalPrime O).primeCompl _ inferInstance
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp : (IsLocalRing.maximalIdeal (verticalDVR O)).IsPrincipal :=
    ⟨⟨algebraMap O[X] (verticalDVR O) (C π),localized_maximalIdeal O π hπ⟩⟩
  have hnf : ¬IsField (verticalDVR O) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (by
      rw [localized_maximalIdeal O π hπ]
      intro h
      exact uniformizer_ne_zero O π hπ ((Ideal.span_eq_bot.mp h) _ (Set.mem_singleton _)))
  exact ((IsDiscreteValuationRing.TFAE (verticalDVR O) hnf).out 4 0).mp hp

/-- The literal coordinate is X at the generic point of the vertical
fiber, not a specialization to the later evaluation point j=1. -/
@[expose] def jV : verticalDVR O := algebraMap O[X] (verticalDVR O) X

private theorem x_sub_c_not_mem (b : O) :
    X - C b ∉ verticalPrime O := by
  intro h
  have h0 : Polynomial.mapRingHom (IsLocalRing.residue O) (X - C b) = 0 :=
    RingHom.mem_ker.mp h
  have h1 := congrArg (fun f : (IsLocalRing.ResidueField O)[X] => f.coeff 1) h0
  have h20 : (1 : IsLocalRing.ResidueField O) = 0 := by
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.coeff_sub, Polynomial.coeff_X_one,
      Polynomial.coeff_C_succ, Polynomial.coeff_zero, sub_zero] using h1
  exact one_ne_zero h20

/-- Every literal X−b is a unit at the generic vertical prime.
In particular j and j−1728 are units even in residue characteristic
2, 3, 11 or 157. -/
theorem j_sub_const_unit (b : O) :
    IsUnit (jV O - algebraMap O[X] (verticalDVR O) (C b)) := by
  rw [jV, ←map_sub]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (verticalDVR O) (verticalPrime O)
    (X - C b)).2 (x_sub_c_not_mem O b)

theorem j_unit : IsUnit (jV O) := by
  simpa only [Polynomial.C_0,map_zero,sub_zero] using j_sub_const_unit O 0

theorem j_minus_1728_unit : IsUnit (jV O - 1728) := by
  have h (n : ℕ) :
      algebraMap O[X] (verticalDVR O) (C (n : O)) = (n : verticalDVR O) := by
    rw [Polynomial.C_eq_natCast,map_natCast]
  exact h 1728 ▸ j_sub_const_unit O (1728 : O)

end SelectedActualVerticalBaseDVR318

#print axioms SelectedActualVerticalBaseDVR318.vertical_isDVR
#print axioms SelectedActualVerticalBaseDVR318.j_minus_1728_unit
#print axioms SelectedActualVerticalBaseDVR318.same_fraction_field
