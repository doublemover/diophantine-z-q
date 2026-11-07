module
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Tactic
public section
noncomputable section
namespace CodimensionOneExtension318
set_option maxHeartbeats 0
variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  [Field K] [Algebra A K] [IsFractionRing A K]

/-- The actual localization at a prime, embedded in the actual fraction field. -/
noncomputable abbrev primeLocalization (P : Ideal A) [P.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

/-- Regularity at an actual prime localization excludes that prime from the
reduced fraction's denominator. The cancellation uses actual UFD reducedness. -/
theorem denominator_not_mem (P : Ideal A) [P.IsPrime] (x : K)
    (hx : x ∈ primeLocalization (K := K) P) :
    (IsFractionRing.den A x : A) ∉ P := by
  obtain ⟨a,s,hs,hx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.zero_mem)
  have hsK : algebraMap A K s ≠ 0 := fun h => hs0 ((IsFractionRing.injective A K) (by simpa using h))
  have hn : x * algebraMap A K (IsFractionRing.den A x) =
      algebraMap A K (IsFractionRing.num A x) :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (x := x) (y := x)).mpr rfl
  have he : IsFractionRing.num A x * s = a * (IsFractionRing.den A x : A) := by
    apply IsFractionRing.injective A K
    simp only [map_mul]
    rw [←hn,hx]
    field_simp
  have hd : (IsFractionRing.den A x : A) ∣ s := by
    apply (IsFractionRing.num_den_reduced A x).symm.dvd_of_dvd_mul_left
    rw [he]
    exact dvd_mul_left _ _
  intro hden
  obtain ⟨c,hc⟩ := hd
  apply hs
  rw [hc]
  exact P.mul_mem_right c hden

/-- A fraction regular at every prime-element localization belongs to the UFD.
No intersection-of-localizations theorem is assumed. -/
theorem integer_of_prime_localizations (x : K)
    (hx : ∀ (p : A) (hp : Prime p),
      letI : (Ideal.span ({p} : Set A)).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
      x ∈ primeLocalization (K := K) (Ideal.span ({p} : Set A))) :
    IsLocalization.IsInteger A x := by
  apply IsFractionRing.isInteger_of_isUnit_den
  by_contra hden
  obtain ⟨p,hp,hpd⟩ := WfDvdMonoid.exists_irreducible_factor hden
    (nonZeroDivisors.coe_ne_zero (IsFractionRing.den A x))
  have hp' : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  letI : (Ideal.span ({p} : Set A)).IsPrime := Ideal.isPrime_span_singleton_of_prime hp'
  have hnot := denominator_not_mem (Ideal.span ({p} : Set A)) x (hx p hp')
  exact hnot (Ideal.mem_span_singleton.mpr hpd)

/-- Codimension-one extension for a Noetherian UFD, using genuine ideal height
and genuine embedded localizations. -/
theorem integer_of_height_one_localizations [IsNoetherianRing A] (x : K)
    (hx : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      x ∈ primeLocalization (K := K) P) : IsLocalization.IsInteger A x := by
  apply integer_of_prime_localizations x
  intro p hp
  letI : (Ideal.span ({p} : Set A)).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  exact hx (Ideal.span ({p} : Set A))
    (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero) hp.not_isUnit)

/-- The exact intersection statement, rather than a supplied Hartogs principle. -/
theorem prime_localizations_iff_integer (x : K) :
    (∀ (p : A) (hp : Prime p),
      letI : (Ideal.span ({p} : Set A)).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
      x ∈ primeLocalization (K := K) (Ideal.span ({p} : Set A))) ↔
    IsLocalization.IsInteger A x := by
  constructor
  · exact integer_of_prime_localizations x
  · rintro ⟨a,rfl⟩ p hp
    letI : (Ideal.span ({p} : Set A)).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    exact (primeLocalization (K := K) (Ideal.span ({p} : Set A))).algebraMap_mem a

/-- Exact codimension-one intersection criterion in the Noetherian UFD case. -/
theorem height_one_localizations_iff_integer [IsNoetherianRing A] (x : K) :
    (∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      x ∈ primeLocalization (K := K) P) ↔ IsLocalization.IsInteger A x := by
  constructor
  · exact integer_of_height_one_localizations x
  · rintro ⟨a,rfl⟩ P hP hheight
    exact (primeLocalization (K := K) P).algebraMap_mem a

/-- Actual coordinatewise extension in any free frame; no finite-dimensional
bound or chosen denominator is needed. -/
theorem free_frame_extension [IsNoetherianRing A] {ι : Type*} (s : ι → K)
    (hs : ∀ i (P : Ideal A) [P.IsPrime], P.height = 1 →
      s i ∈ primeLocalization (K := K) P) :
    ∃ r : ι → A, ∀ i, algebraMap A K (r i) = s i := by
  have hh : ∀ i, ∃ r : A, algebraMap A K r = s i := fun i =>
    integer_of_height_one_localizations (s i) (hs i)
  choose r hr using hh
  exact ⟨r,hr⟩

/-- The extended coefficients are unique; in particular independently produced
free-frame extensions agree wherever their fraction-field sections agree. -/
theorem free_frame_extension_unique [IsNoetherianRing A] {ι : Type*} (s : ι → K)
    (hs : ∀ i (P : Ideal A) [P.IsPrime], P.height = 1 →
      s i ∈ primeLocalization (K := K) P) :
    ∃! r : ι → A, ∀ i, algebraMap A K (r i) = s i := by
  obtain ⟨r,hr⟩ := free_frame_extension s hs
  refine ⟨r,hr,?_⟩
  intro r' hr'
  funext i
  exact IsFractionRing.injective A K ((hr' i).trans (hr i).symm)

end CodimensionOneExtension318
