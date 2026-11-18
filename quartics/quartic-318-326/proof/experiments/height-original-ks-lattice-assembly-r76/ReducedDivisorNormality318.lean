module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ReducedDivisorNormality318
open Polynomial
variable {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L]
  (p : R) [IsReduced (R ⧸ Ideal.span {p})]

/-- A reduced divisor detects divisibility of a numerator of an integral
element. No primality of p or Noetherian condition is needed. -/
theorem numerator_dvd (hinj : Function.Injective (algebraMap R L))
    {x : L} (hx : IsIntegral R x) {a : R}
    (ha : algebraMap R L p * x = algebraMap R L a) : p ∣ a := by
  let J : Ideal R := Ideal.span {p}
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  by_cases hQ : Subsingleton (R ⧸ J)
  · letI := hQ
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim (q a) 0))
  · letI : Nontrivial (R ⧸ J) := not_subsingleton_iff_nontrivial.mp hQ
    obtain ⟨f, hf, hfx⟩ := hx
    have hK : aeval (algebraMap R L a) (f.scaleRoots p) = 0 := by
      simpa only [ha] using (Polynomial.scaleRoots_aeval_eq_zero (r := p) hfx)
    have hR : (f.scaleRoots p).eval a = 0 := by
      apply hinj
      simpa only [Polynomial.aeval_def, Polynomial.eval₂_at_apply, map_zero] using hK
    have hpq : q p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton p))
    have hpoly : (f.scaleRoots p).map q = X ^ (f.map q).natDegree := by
      rw [Polynomial.map_scaleRoots f p q (by rw [hf, map_one]; exact one_ne_zero),
        hpq, Polynomial.scaleRoots_zero, (hf.map q)]
      simp
    have hqa : q a ^ (f.map q).natDegree = 0 := by
      have he : ((f.scaleRoots p).map q).eval (q a) = 0 := by
        rw [Polynomial.eval_map_apply, hR, map_zero]
      simpa only [hpoly, Polynomial.eval_pow, Polynomial.eval_X] using he
    have hz : q a = 0 := isNilpotent_iff_eq_zero.mp ⟨_, hqa⟩
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Integral elements whose only denominator is a power of p already
belong to R when the divisor quotient is reduced. -/
theorem image_of_power_denominator (hp : p ≠ 0)
    (hinj : Function.Injective (algebraMap R L)) {x : L} (hx : IsIntegral R x)
    (n : ℕ) (a : R) (ha : algebraMap R L p ^ n * x = algebraMap R L a) :
    ∃ b : R, algebraMap R L b = x := by
  induction n generalizing a with
  | zero => exact ⟨a, by simpa only [pow_zero, one_mul] using ha.symm⟩
  | succ n ih =>
    have hy : IsIntegral R (algebraMap R L (p ^ n) * x) :=
      (isIntegral_algebraMap (R := R) (A := L)).mul hx
    have hpa : algebraMap R L p * (algebraMap R L (p ^ n) * x) = algebraMap R L a := by
      simpa only [map_pow, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ha
    obtain ⟨b, hb⟩ := numerator_dvd p hinj hy hpa
    apply ih b
    apply mul_left_cancel₀ (show algebraMap R L p ≠ 0 from
      fun h => hp (hinj (by simpa only [map_zero] using h)))
    calc
      algebraMap R L p * (algebraMap R L p ^ n * x) = algebraMap R L a := by
        simpa only [map_pow] using hpa
      _ = algebraMap R L p * algebraMap R L b := by rw [hb, map_mul]

/-- Normality descends from the p-inverted ring after reducedness of the
actual quotient removes denominator powers. The generic ambient field and
localization/tower hypotheses are explicit, not original-specific premises. -/
theorem normal_of_away (hp : p ≠ 0) (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [IsLocalization.Away p S] [Algebra S L] [IsScalarTower R S L]
    [IsFractionRing R L] [IsFractionRing S L] [IsIntegrallyClosed S] :
    IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff L).mpr
  intro x hx
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff L).mp (inferInstance : IsIntegrallyClosed S)
    (hx.tower_top : IsIntegral S x)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj p z
  apply image_of_power_denominator p hp (IsFractionRing.injective R L) hx n a
  have he := congrArg (algebraMap S L) ha
  simpa only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S L, hz, mul_comm] using he

end ReducedDivisorNormality318
