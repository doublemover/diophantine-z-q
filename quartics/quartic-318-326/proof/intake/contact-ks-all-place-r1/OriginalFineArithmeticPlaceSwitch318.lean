module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace OriginalFineArithmeticPlaceSwitch318

open scoped nonZeroDivisors
open IsDedekindDomain

/-- Only the two genuine fine levels on the complementary base opens. -/
inductive Lane
  | three
  | eleven
  deriving DecidableEq

def denominator : Lane→ℤ
  | .three => 3
  | .eleven => 11

theorem denominator_nonzero (i : Lane) : denominator i≠0 := by
  cases i <;> decide

abbrev IntegerBase (i : Lane) := Localization.Away (denominator i)

variable {O E : Type*} [CommRing O] [IsDomain O] [IsDedekindDomain O]
  [Field E] [CharZero E] [Algebra O E] [IsFractionRing O E]

variable (w : HeightOneSpectrum O)

abbrev localInt : Subalgebra O E :=
  Localization.subalgebra E w.asIdeal.primeCompl
    w.asIdeal.primeCompl_le_nonZeroDivisors

instance actual_fraction : IsFractionRing (localInt (E:=E) w) E :=
  Localization.subalgebra.isFractionRing E _ _

instance actual_localization :
    IsLocalization.AtPrime (localInt (E:=E) w) w.asIdeal :=
  Localization.subalgebra.isLocalization_subalgebra E _ _

instance actual_DVR : IsDiscreteValuationRing (localInt (E:=E) w) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O w.ne_bot _

/-- This test is at the actual prime ideal of O_E, not a test on
the rational coarse coordinate or on an independent completion. -/
def selected : Lane := by
  classical
  exact if (3:O) ∈ w.asIdeal then .eleven else .three

theorem at_three (h : (3:O)∈w.asIdeal) : selected w=.eleven := by
  classical
  simp only [selected,if_pos h]

theorem away_from_three (h : (3:O)∉w.asIdeal) : selected w=.three := by
  classical
  simp only [selected,if_neg h]

theorem exactly_three : selected w=.eleven ↔ (3:O)∈w.asIdeal := by
  classical
  by_cases h : (3:O)∈w.asIdeal
  · rw [at_three w h]
    simp [h]
  · rw [away_from_three w h]
    simp [h]

theorem eleven_away_from_prime_above_three (h : (3:O)∈w.asIdeal) :
    (11:O)∉w.asIdeal := by
  intro h11
  have h1 := w.asIdeal.sub_mem (w.asIdeal.mul_mem_right (4:O) h) h11
  rw [show (3:O)*4-11=1 by norm_num] at h1
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one w.asIdeal).2 h1)

theorem chosen_denominator_outside :
    ((denominator (selected w):ℤ):O)∉w.asIdeal := by
  classical
  by_cases h : (3:O)∈w.asIdeal
  · rw [at_three w h]
    simpa only [denominator, Int.cast_ofNat] using eleven_away_from_prime_above_three w h
  · rw [away_from_three w h]
    simpa only [denominator, Int.cast_ofNat] using h

theorem chosen_denominator_unit :
    IsUnit ((denominator (selected w):ℤ):localInt (E:=E) w) := by
  have u := IsLocalization.map_units (localInt (E:=E) w)
    (⟨((denominator (selected w):ℤ):O),chosen_denominator_outside w⟩:
      w.asIdeal.primeCompl)
  simpa only [map_intCast] using u

def actualBase : IntegerBase (selected w)→+*localInt (E:=E) w :=
  IsLocalization.Away.lift (denominator (selected w))
    (g:=Int.castRingHom (localInt (E:=E) w)) (chosen_denominator_unit (E:=E) w)

def oldFieldBase (i : Lane) : IntegerBase i→+*E :=
  IsLocalization.Away.lift (denominator i) (g:=Int.castRingHom E)
    (isUnit_iff_ne_zero.2 (Int.cast_ne_zero.mpr (denominator_nonzero i)))

/-- A literal scheme-base square: the same E inclusion commutes
with the selected integer-base map, also at ramified primes. -/
theorem keeps_generic_base :
    (algebraMap (localInt (E:=E) w) E).comp (actualBase (E:=E) w)=oldFieldBase (E:=E) (selected w) := by
  apply IsLocalization.ringHom_ext (.powers (denominator (selected w)))
  ext z
  change algebraMap (localInt (E:=E) w) E
    (actualBase (E:=E) w (algebraMap ℤ (IntegerBase (selected w)) z))=
    oldFieldBase (E:=E) (selected w) (algebraMap ℤ (IntegerBase (selected w)) z)
  simp only [actualBase, oldFieldBase, IsLocalization.Away.lift_eq, map_intCast]

end OriginalFineArithmeticPlaceSwitch318
