module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
noncomputable section
namespace IntegralSquareInertia318
open NumberField
open scoped NumberField
set_option maxHeartbeats 600000
attribute [-instance] DivisionRing.toRatAlgebra
variable {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
abbrev G := L ≃ₐ[ℚ] L

omit [NumberField L] in
/-- Actual ideal-theoretic inertia cannot change an integral square root
whose square and two are nonzero modulo the specified prime. -/
theorem inertia_fixes_integral_square (P : Ideal (𝓞 L)) [P.IsPrime]
    (h2 : (2 : 𝓞 L) ∉ P) (x : 𝓞 L) (b : ℤ) (hx : x^2 = (b : 𝓞 L))
    (hb : (b : 𝓞 L) ∉ P) (s : G (L := L)) (hs : s ∈ P.inertia (G (L := L))) :
    s • x = x := by
  have he : (s • x)^2 = x^2 := by
    rw [← smul_pow', hx]
    exact map_intCast (MulSemiringAction.toRingHom (G (L := L)) (𝓞 L) s) b
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact h
  · have hi := (Ideal.mem_inertia.mp hs) x
    rw [h] at hi
    have hm : (2 : 𝓞 L) * x ∈ P := by
      have hn := P.neg_mem hi
      convert hn using 1; ring
    have hxp : x ∈ P := ((inferInstance : P.IsPrime).mem_or_mem hm).resolve_left h2
    exact False.elim (hb (hx ▸ P.pow_mem_of_mem hxp 2 (by decide)))

omit [Algebra ℚ L] in
/-- Remove exactly the even p-part of an integer square equation, inside
the same number field, producing an actual integral normalized root. -/
theorem normalized_integral_root (p : ℕ) [Fact p.Prime] (b : ℤ) (hb : b ≠ 0)
    (he : Even (padicValInt p b)) (x : L) (hx : x^2 = (b : L)) :
    ∃ (m : ℕ) (c : ℤ) (z : 𝓞 L), b = (p : ℤ)^(2*m)*c ∧ ¬(p : ℤ) ∣ c ∧
      z^2 = (c : 𝓞 L) ∧ x = (p : L)^m * (z : L) := by
  obtain ⟨m, hm⟩ := he
  have hv : multiplicity (p : ℤ) b = 2*m := by
    rw [← padicValInt.of_ne_one_ne_zero, hm]
    omega
  obtain ⟨c, hc, hpc⟩ := ((padicValRat.finite_int_prime_iff (p := p)).mpr hb).exists_eq_pow_mul_and_not_dvd
  rw [hv] at hc
  have hp : (p : L) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let y : L := x / (p : L)^m
  have hy : y^2 = (c : L) := by
    dsimp [y]
    rw [div_pow, hx]
    have hcL : (b : L) = (p : L)^(2*m) * (c : L) := by exact_mod_cast hc
    rw [hcL, Nat.mul_comm 2 m, pow_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ hp))
  have hyi : IsIntegral ℤ y := by
    apply IsIntegral.of_pow (show 0 < 2 by decide)
    rw [hy]
    exact isIntegral_algebraMap
  refine ⟨m, c, ⟨y, hyi⟩, hc, hpc, ?_, ?_⟩
  · apply RingOfIntegers.ext
    exact hy
  · change x = (p : L)^m * (x / (p : L)^m)
    field_simp

omit [NumberField L] [Algebra ℚ L] in
/-- The actual prime above p detects precisely p-divisibility of integers. -/
lemma integer_mem_iff (p : ℕ) (P : Ideal (𝓞 L))
    (hover : P.under ℤ = Ideal.span {(p : ℤ)}) (n : ℤ) :
    (n : 𝓞 L) ∈ P ↔ (p : ℤ) ∣ n := by
  change algebraMap ℤ (𝓞 L) n ∈ P ↔ _
  rw [← Ideal.mem_under, hover, Ideal.mem_span_singleton]

/-- Actual inertia fixes every root of an integer whose p-valuation is even.
The normalized root is constructed in the same ring of integers. -/
theorem inertia_fixes_even_square (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hover : P.under ℤ = Ideal.span {(p : ℤ)})
    (h2 : ¬(p : ℤ) ∣ 2) (b : ℤ) (hb : b ≠ 0) (he : Even (padicValInt p b))
    (x : L) (hx : x^2 = (b : L)) (s : G (L := L))
    (hs : s ∈ P.inertia (G (L := L))) : s x = x := by
  obtain ⟨m, c, z, _, hpc, hz, hxz⟩ := normalized_integral_root p b hb he x hx
  have h2P : (2 : 𝓞 L) ∉ P := by
    simpa only [Int.cast_ofNat] using (integer_mem_iff p P hover 2).not.mpr h2
  have hcP : (c : 𝓞 L) ∉ P := (integer_mem_iff p P hover c).not.mpr hpc
  have hfixed := inertia_fixes_integral_square P h2P z c hz hcP s hs
  have hzL : s (z : L) = (z : L) :=
    congrArg (fun w : 𝓞 L => (w : L)) hfixed
  rw [hxz, map_mul, map_pow, map_natCast, hzL]

end IntegralSquareInertia318
