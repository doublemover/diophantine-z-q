module
public import SelectedVerticalHorizontalPrincipalPrime318
public import SelectedOriginalLiteralScalarUniqueness318
import all SelectedPrincipalPrimeNormalIntersection318
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section

open Polynomial
open SelectedPrincipalPrimeNormalIntersection318 SelectedVerticalHorizontalPrincipalPrime318
open SelectedOriginalLiteralScalarUniqueness318

namespace SelectedHorizontalOriginalScalar318

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (q : PrimeSpectrum O[X])
local notation "R" => localRing q

/-- The localization of the actual principal prime of O[J]. -/
theorem local_isDVR (hq : principalPrime q) : IsDiscreteValuationRing R := by
  letI : IsNoetherianRing R := IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  obtain ⟨π,hπ,hq'⟩ := hq
  have hexact : IsLocalRing.maximalIdeal R = Ideal.span ({algebraMap O[X] R π}:Set R) := by
    calc
      IsLocalRing.maximalIdeal R = q.asIdeal.map (algebraMap O[X] R) :=
        Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = _ :=
        (congrArg (fun I : Ideal O[X] => I.map (algebraMap O[X] R)) hq').trans
          (by rw [Ideal.map_span,Set.image_singleton])
  have hp : (IsLocalRing.maximalIdeal R).IsPrincipal :=
    ⟨⟨algebraMap O[X] R π,hexact⟩⟩
  have hπ0 : algebraMap O[X] R π ≠ 0 := by
    have hi := IsLocalization.injective R q.asIdeal.primeCompl_le_nonZeroDivisors
    exact fun hz => hπ.ne_zero (hi (hz.trans (map_zero _).symm))
  have hnf : ¬IsField R :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (by
      rw [hexact]
      intro h
      exact hπ0 ((Ideal.span_eq_bot.mp h) _ (Set.mem_singleton _)))
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp hp

variable (hor : ∀ b : O, b≠0 → C b ∉ q.asIdeal)

include hor in
/-- The coefficient O embeds injectively into the actual residue
field of a horizontal localization. In particular residue is char 0. -/
theorem horizontal_residueCharZero : CharZero (IsLocalRing.ResidueField R) := by
  let f : O →+* IsLocalRing.ResidueField R :=
    (IsLocalRing.residue R).comp ((algebraMap O[X] R).comp Polynomial.C)
  have hf : Function.Injective f := by
    intro a b he
    by_contra hne
    have hu : IsUnit (algebraMap O[X] R (C (a-b))) :=
      horizontal_coeff_unit O q hor (a-b) (sub_ne_zero.mpr hne)
    have hf0 : f (a-b)=0 := by rw [map_sub,he,sub_self]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu hf0
  constructor
  intro a b he
  have ht : Function.Injective (fun n : ℕ => (n:O)) := Nat.cast_injective
  apply ht
  apply hf
  simpa only [map_natCast] using he

/-- The actual J in this localization, not j=1. -/
@[expose] def localJ : R := algebraMap O[X] R X

theorem localJ_mem (h : (X : O[X]) ∈ q.asIdeal) :
    localJ q ∈ IsLocalRing.maximalIdeal R :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff R q.asIdeal X).2 h

theorem localJ_sub_mem (h : (X - 1728 : O[X]) ∈ q.asIdeal) :
    localJ q - 1728 ∈ IsLocalRing.maximalIdeal R := by
  have hh := (IsLocalization.AtPrime.to_map_mem_maximal_iff R q.asIdeal
    (X - 1728 : O[X])).2 h
  simpa only [localJ,map_sub,map_ofNat] using hh

include hor in
private theorem nat_unit (a : ℕ) (ha : a≠0) : IsUnit (a:R) := by
  have h := horizontal_coeff_unit O q hor (a:O) (Nat.cast_ne_zero.mpr ha)
  simpa only [Polynomial.C_eq_natCast,map_natCast] using h

variable (M : ℕ) (hM : M≠0)
variable (h0 : (X : O[X]) ∉ q.asIdeal) (h1728 : (X - 1728 : O[X]) ∉ q.asIdeal)

include hor hM h0 h1728 in
/-- Outside the two horizontal collision sections, the genuine
integer coefficient chart maps into the same localized trait:
6, M, J and J−1728 are all genuine units. -/
def localScalar : OpenJModel318.Base M →+* R :=
  IsLocalization.Away.lift
    (g:=Polynomial.eval₂RingHom (Int.castRingHom R) (localJ q))
    (OpenJModel318.denominator M) (by
      have h6 : IsUnit (6:R) := nat_unit q hor 6 (by decide)
      have hJ : IsUnit (localJ q) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff R q.asIdeal X).2 h0
      have hd : IsUnit (localJ q-1728) := by
        have h := (IsLocalization.AtPrime.isUnit_to_map_iff R q.asIdeal (X-1728:O[X])).2 h1728
        simpa only [localJ,map_sub,map_ofNat] using h
      simp only [OpenJModel318.denominator,Polynomial.coe_eval₂RingHom,
        eval₂_mul,eval₂_sub,eval₂_natCast,eval₂_ofNat,eval₂_X]
      exact (((h6.mul (nat_unit q hor M hM)).mul hJ).mul hd))

theorem localScalar_j :
    localScalar q hor M hM h0 h1728 (OpenJModel318.jCoord M)=localJ q := by
  unfold localScalar OpenJModel318.jCoord
  rw [IsLocalization.Away.lift_eq] <;> exact eval₂_X _ _

variable {K : Type*} [Field K] [Algebra O[X] K] [IsFractionRing O[X] K]

attribute [local instance] SelectedPrincipalPrimeNormalIntersection318.localAlgebra

/-- Linking the exact same polynomial and same generator: this local
coefficient map equals the global one after passage to the common
generic field. -/
theorem matches_global (c : OpenJModel318.Base M →+* K)
    (hc : c (OpenJModel318.jCoord M)=algebraMap O[X] K X) :
    (algebraMap R K).comp (localScalar q hor M hM h0 h1728)=c := by
  apply over_original_j_eq
  rw [RingHom.comp_apply,localScalar_j,hc]
  exact (IsScalarTower.algebraMap_apply O[X] R K X).symm

end SelectedHorizontalOriginalScalar318

#print axioms SelectedHorizontalOriginalScalar318.horizontal_residueCharZero
#print axioms SelectedHorizontalOriginalScalar318.localScalar_j
#print axioms SelectedHorizontalOriginalScalar318.matches_global
