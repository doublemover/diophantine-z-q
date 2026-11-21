module
public import SelectedActualVerticalBaseDVR318
public import SelectedPrincipalPrimeNormalIntersection318
import all SelectedPrincipalPrimeNormalIntersection318
public section
noncomputable section

open Polynomial
open SelectedActualVerticalBaseDVR318 SelectedPrincipalPrimeNormalIntersection318

namespace SelectedVerticalHorizontalPrincipalPrime318

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Every actual principal prime of the affine arithmetic J-line is
the genuine vertical prime or is horizontal, with all nonzero
coefficient constants invertible after localization. -/
theorem vertical_or_horizontal (q : PrimeSpectrum O[X]) (hq : principalPrime q) :
    q.asIdeal = verticalPrime O ∨
      ∀ b : O, b ≠ 0 → C b ∉ q.asIdeal := by
  let P := q.asIdeal.comap (Polynomial.C : O →+* O[X])
  letI : P.IsPrime := Ideal.comap_isPrime (Polynomial.C : O →+* O[X]) q.asIdeal
  by_cases hP : P=⊥
  · right
    intro b hb hz
    have ht : b ∈ P := hz
    rw [hP,Ideal.mem_bot] at ht
    exact hb ht
  · left
    have hunique := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      (inferInstance : IsDiscreteValuationRing O)).2
    have hmax : P=IsLocalRing.maximalIdeal O :=
      hunique.unique ⟨hP,inferInstance⟩ ⟨IsDiscreteValuationRing.not_a_field O,inferInstance⟩
    obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hπP : π∈P := by
      rw [hmax,hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    obtain ⟨p,hp,hq'⟩ := hq
    have hπq : C π ∈ q.asIdeal := hπP
    have hdiv : p ∣ C π := Ideal.mem_span_singleton.mp (hq' ▸ hπq)
    have hspan : (Ideal.span ({C π}:Set O[X])).IsPrime := by
      rw [←prime_eq_span O π hπ]
      infer_instance
    have hsv : Prime (C π) :=
      (Ideal.span_singleton_prime (Polynomial.C_ne_zero.mpr hπ.ne_zero)).mp hspan
    have hassoc : Associated (C π) p :=
      (hsv.irreducible.dvd_iff.mp hdiv).resolve_left hp.not_isUnit
    calc
      q.asIdeal = Ideal.span ({p}:Set O[X]) := hq'
      _ = Ideal.span ({C π}:Set O[X]) := Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm
      _ = verticalPrime O := (prime_eq_span O π hπ).symm

/-- Thus the literal map of every nonzero coefficient becomes a
unit on a horizontal localization. This is not true at the vertical
prime, so it must not be used before taking the dichotomy. -/
theorem horizontal_coeff_unit (q : PrimeSpectrum O[X])
    (hq : ∀ b : O, b≠0 → C b ∉ q.asIdeal) (b : O) (hb : b≠0) :
    IsUnit (algebraMap O[X] (localRing q) (C b)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (localRing q) q.asIdeal (C b)).2 (hq b hb)

end SelectedVerticalHorizontalPrincipalPrime318

#print axioms SelectedVerticalHorizontalPrincipalPrime318.vertical_or_horizontal
#print axioms SelectedVerticalHorizontalPrincipalPrime318.horizontal_coeff_unit
