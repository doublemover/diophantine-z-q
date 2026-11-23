module
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Ring
public section

/-! Descent of a whole generic-fibre coefficient along a reduced fibre.
No integral-domain, normality, or Noetherian hypothesis. -/
namespace OriginalReducedFibreSaturation318

variable {R : Type*} [CommRing R]

/-- A clearing denominator outside each minimal prime over the special fibre. -/
def Clears (p a : R) (n : ℕ) : Prop :=
  ∀ (q : Ideal R), (Ideal.span ({p} : Set R)).IsMinimalPrime q →
    ∃ s : R, s ∉ q ∧ ∃ c : R, s * a = p ^ n * c

/-- The localized numerator is a multiple of the same power at every component generic. -/
def AtGenerics (p a : R) (n : ℕ) : Prop :=
  ∀ (q : Ideal R) (hq : (Ideal.span ({p} : Set R)).IsMinimalPrime q),
    letI : q.IsPrime := hq.isPrime
    algebraMap R (Localization q.primeCompl) a ∈
      (Ideal.span ({p ^ n} : Set R)).map (algebraMap R (Localization q.primeCompl))

theorem atGenerics_iff_clears (p a : R) (n : ℕ) :
    AtGenerics p a n ↔ Clears p a n := by
  constructor
  · intro h q hq
    let : q.IsPrime := hq.isPrime
    obtain ⟨s, hs, ha⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
        (Localization q.primeCompl) (Ideal.span ({p ^ n} : Set R)) a).mp (h q hq)
    exact ⟨s, hs, Ideal.mem_span_singleton.mp ha⟩
  · intro h q hq
    let : q.IsPrime := hq.isPrime
    obtain ⟨s, hs, c, hc⟩ := h q hq
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization q.primeCompl) (Ideal.span ({p ^ n} : Set R)) a).mpr
        ⟨s, hs, Ideal.mem_span_singleton.mpr ⟨c, hc⟩⟩

/-- An actual stalk value in R_q agreeing with the generic numerator after
inverting p gives a clearing witness, even if R has zero divisors. The
additional factor t outside q cannot in general be cancelled from R. -/
theorem clears_at_prime_of_stalk_lift {p a : R} (hp : IsRegular p) (n : ℕ)
    (q : Ideal R) [q.IsPrime] {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization q.primeCompl A] {B : Type*} [CommRing B] [Algebra A B]
    [IsLocalization.Away (algebraMap R A p) B] (y : A)
    (h : algebraMap A B (algebraMap R A a) =
      algebraMap A B (algebraMap R A p ^ n * y)) :
    ∃ s : R, s ∉ q ∧ ∃ c : R, s * a = p ^ n * c := by
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj q.primeCompl y
  change y * algebraMap R A (s : R) = algebraMap R A c at hcs
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (algebraMap R A p) h
  have he : algebraMap R A (p ^ k * ((s : R) * a)) =
      algebraMap R A (p ^ k * (p ^ n * c)) := by
    simp only [map_mul, map_pow]
    calc
      _ = (algebraMap R A p ^ k * algebraMap R A a) * algebraMap R A (s : R) := by ring
      _ = (algebraMap R A p ^ k * (algebraMap R A p ^ n * y)) *
          algebraMap R A (s : R) := by rw [hk]
      _ = algebraMap R A p ^ k * (algebraMap R A p ^ n *
          (y * algebraMap R A (s : R))) := by ring
      _ = _ := by rw [hcs]
  obtain ⟨t, ht⟩ := IsLocalization.exists_of_eq (M := q.primeCompl) he
  refine ⟨(t : R) * (s : R), q.primeCompl.mul_mem t.2 s.2, (t : R) * c, (hp.pow k).left ?_⟩
  calc
    p ^ k * (((t : R) * (s : R)) * a) = (t : R) * (p ^ k * ((s : R) * a)) := by ring
    _ = (t : R) * (p ^ k * (p ^ n * c)) := ht
    _ = p ^ k * (p ^ n * ((t : R) * c)) := by ring

theorem divisibility_at_reduced_fibre {p : R} (hp : IsRegular p)
    (hred : IsReduced (R ⧸ Ideal.span ({p} : Set R))) {n : ℕ} {a : R}
    (h : Clears p a n) : p ^ n ∣ a := by
  let I : Ideal R := Ideal.span ({p} : Set R)
  have hr : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).mpr hred
  induction n generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
    have hm : a ∈ I.radical := by
      rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
      intro q hq
      have hmin : I.IsMinimalPrime q := hq
      obtain ⟨s, hs, c, he⟩ := h q hmin
      have hpq : p ∈ q := hmin.le (Ideal.mem_span_singleton_self p)
      have hsa : s * a ∈ q := by
        rw [he, pow_succ', mul_assoc]
        exact q.mul_mem_right _ hpq
      exact (hmin.isPrime.mem_or_mem hsa).resolve_left hs
    have hsub : I.radical ≤ I := hr.radical_le_iff.mpr le_rfl
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hsub hm)
    have hlow : Clears p b n := by
      intro q hq
      obtain ⟨s, hs, c, he⟩ := h q hq
      refine ⟨s, hs, c, hp.left ?_⟩
      calc
        p * (s * b) = s * a := by rw [hb]; ring
        _ = p ^ (n + 1) * c := he
        _ = p * (p ^ n * c) := by rw [pow_succ', mul_assoc]
    obtain ⟨z, hz⟩ := ih hlow
    exact ⟨z, by rw [hb, hz, pow_succ', mul_assoc]⟩

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Tests on presentations of an element of the actual generic open D(p). -/
def IntegralAtGenerics (p : R) (x : S) : Prop :=
  ∀ (n : ℕ) (a : R), x * algebraMap R S p ^ n = algebraMap R S a → AtGenerics p a n

theorem away_injective {p : R} (hp : IsRegular p) [IsLocalization.Away p S] :
    Function.Injective (algebraMap R S) := by
  intro a b hab
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq p hab
  exact (hp.pow n).left hn

/-- The input is a section on the whole generic open, not an arbitrary rational
function. The regular lift is unique even when the total space is disconnected. -/
theorem extend_generic {p : R} (hp : IsRegular p)
    (hred : IsReduced (R ⧸ Ideal.span ({p} : Set R))) [IsLocalization.Away p S]
    (x : S) (hx : IntegralAtGenerics p x) :
    ∃! z : R, algebraMap R S z = x := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj p x
  have hc := (atGenerics_iff_clears p a n).mp (hx n a ha)
  obtain ⟨z, hz⟩ := divisibility_at_reduced_fibre hp hred hc
  have hpow : IsUnit (algebraMap R S p ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit (S := S) p).pow n
  have hzx : algebraMap R S z = x := by
    apply hpow.mul_left_cancel
    calc
      algebraMap R S p ^ n * algebraMap R S z = algebraMap R S a := by rw [hz, map_mul, map_pow]
      _ = x * algebraMap R S p ^ n := ha.symm
      _ = algebraMap R S p ^ n * x := mul_comm _ _
  exact ⟨z, hzx, fun b hb => away_injective hp (hb.trans hzx.symm)⟩

/-- Both local lifts occur in the same original rings. The inverse identity
reflects through the same injective generic restriction, without a fraction field. -/
theorem extend_generic_unit {p : R} (hp : IsRegular p)
    (hred : IsReduced (R ⧸ Ideal.span ({p} : Set R))) [IsLocalization.Away p S]
    (u : Sˣ) (hu : IntegralAtGenerics p (u : S))
    (hv : IntegralAtGenerics p (↑(u⁻¹) : S)) :
    ∃ z : Rˣ, algebraMap R S (z : R) = (u : S) ∧
      algebraMap R S (↑(z⁻¹) : R) = (↑(u⁻¹) : S) := by
  obtain ⟨a, ha, _⟩ := extend_generic hp hred (u : S) hu
  obtain ⟨b, hb, _⟩ := extend_generic hp hred (↑(u⁻¹) : S) hv
  have hab : a * b = 1 := by
    apply away_injective (S := S) hp
    rw [map_mul, map_one, ha, hb]
    exact u.val_inv
  exact ⟨⟨a, b, hab, by rwa [mul_comm]⟩, ha, hb⟩

end OriginalReducedFibreSaturation318
