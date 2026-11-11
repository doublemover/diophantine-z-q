module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace ThreeProjectiveJCertificates318
open Polynomial

/-- The degree-four pair for the actual level-three j formula. -/
@[expose] def homogeneousNumerator {R : Type*} [CommRing R] (x y : R) : R :=
  (x + 27*y) * (x + 243*y)^3
@[expose] def homogeneousDenominator {R : Type*} [CommRing R] (x y : R) : R :=
  x^3*y

lemma numerator_scale {R : Type*} [CommRing R] (a x y : R) :
    homogeneousNumerator (a*x) (a*y) = a^4 * homogeneousNumerator x y := by
  unfold homogeneousNumerator
  ring

lemma denominator_scale {R : Type*} [CommRing R] (a x y : R) :
    homogeneousDenominator (a*x) (a*y) = a^4 * homogeneousDenominator x y := by
  unfold homogeneousDenominator
  ring

/-- Exact overlap identity over any ring where the two coordinates are
inverse. The common factor is retained rather than silently canceled. -/
theorem chart_pair_overlap {R : Type*} [CommRing R] (t s : R) (hts : t*s=1) :
    homogeneousNumerator t 1 = t^4 * homogeneousNumerator 1 s ∧
      homogeneousDenominator t 1 = t^4 * homogeneousDenominator 1 s := by
  constructor
  · simpa only [mul_one,hts] using numerator_scale t 1 s
  · simpa only [mul_one,hts] using denominator_scale t 1 s

@[expose] def finiteNumerator : ℚ[X] := (X+27)*(X+243)^3
@[expose] def finiteDenominator : ℚ[X] := X^3
@[expose] def reciprocalNumerator : ℚ[X] := (1+27*X)*(1+243*X)^3
@[expose] def reciprocalDenominator : ℚ[X] := X

@[expose] def finiteBezoutA : ℚ[X] := 38*X^2-972*X+19683
@[expose] def finiteBezoutB : ℚ[X] := 38*X^3+27756*X^2+6764391*X+550572876
@[expose] def reciprocalBezoutB : ℚ[X] :=
  756+196830*X+19131876*X^2+387420489*X^3

/-- The finite-chart certificate exposes exactly the power of 3 that must
be invertible. It is not an integral coprimality assertion. -/
theorem finite_bezout :
    finiteBezoutA*finiteNumerator-finiteBezoutB*finiteDenominator = (3:ℚ[X])^27 := by
  unfold finiteBezoutA finiteBezoutB finiteNumerator finiteDenominator
  ring

theorem reciprocal_bezout :
    reciprocalNumerator-reciprocalBezoutB*reciprocalDenominator = 1 := by
  unfold reciprocalNumerator reciprocalBezoutB reciprocalDenominator
  ring

theorem finite_coprime : IsCoprime finiteNumerator finiteDenominator := by
  let c : ℚ[X] := C (((3:ℚ)^27)⁻¹)
  refine ⟨c*finiteBezoutA,-c*finiteBezoutB,?_⟩
  calc
    c*finiteBezoutA*finiteNumerator+(-c*finiteBezoutB)*finiteDenominator =
        c*(finiteBezoutA*finiteNumerator-finiteBezoutB*finiteDenominator) := by ring
    _ = c*(3:ℚ[X])^27 := by rw [finite_bezout]
    _ = 1 := by
      have h3 : (3:ℚ[X])^27 = C ((3:ℚ)^27) := by
        simp only [map_pow,map_ofNat]
      rw [h3]
      change C (((3:ℚ)^27)⁻¹) * C ((3:ℚ)^27) = 1
      rw [←map_mul,inv_mul_cancel₀ (by norm_num),map_one]

theorem reciprocal_coprime : IsCoprime reciprocalNumerator reciprocalDenominator := by
  refine ⟨1,-reciprocalBezoutB,?_⟩
  simpa only [one_mul,neg_mul,sub_eq_add_neg] using reciprocal_bezout

lemma basicOpen_cover_of_coprime {R : Type*} [CommRing R] {f g : R}
    (h : IsCoprime f g) : PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g = ⊤ := by
  apply le_antisymm le_top
  intro p _
  change f ∉ p.asIdeal ∨ g ∉ p.asIdeal
  by_cases hf : f ∈ p.asIdeal
  · right
    intro hg
    obtain ⟨a,b,hab⟩ := h
    have h1 : (1:R) ∈ p.asIdeal := by
      rw [←hab]
      exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left a hf) (p.asIdeal.mul_mem_left b hg)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal h1 isUnit_one)
  · exact Or.inl hf

/-- The two target-coordinate choices cover every prime of the full finite
source chart over Q, not just its complex-valued points. -/
theorem finite_basicOpen_cover :
    PrimeSpectrum.basicOpen finiteNumerator ⊔
      PrimeSpectrum.basicOpen finiteDenominator = ⊤ :=
  basicOpen_cover_of_coprime finite_coprime

/-- The reciprocal source chart is covered too, including its origin. -/
theorem reciprocal_basicOpen_cover :
    PrimeSpectrum.basicOpen reciprocalNumerator ⊔
      PrimeSpectrum.basicOpen reciprocalDenominator = ⊤ :=
  basicOpen_cover_of_coprime reciprocal_coprime

/-- On nonzero homogeneous pairs in characteristic zero, the two homogeneous
coordinates never vanish simultaneously. -/
theorem no_common_zero {K : Type*} [Field K] [CharZero K] (x y : K)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    ¬(homogeneousNumerator x y=0 ∧ homogeneousDenominator x y=0) := by
  rintro ⟨hn,hd⟩
  change x^3*y=0 at hd
  rcases mul_eq_zero.mp hd with hx | hy
  · have hx0 : x=0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx
    subst x
    have hy : y ≠ 0 := hxy.resolve_left (by simp)
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (27:K) ≠ 0) hy)
      (pow_ne_zero _ (mul_ne_zero (by norm_num : (243:K) ≠ 0) hy)))
      (by simpa only [homogeneousNumerator,zero_add] using hn)
  · subst y
    have hx : x ≠ 0 := hxy.resolve_right (by simp)
    exact (mul_ne_zero hx (pow_ne_zero 3 hx))
      (by simpa only [homogeneousNumerator,mul_zero,add_zero] using hn)

/-- The same pair really does have a base point in characteristic 3. Hence
the Q-model certificates cannot justify an everywhere-defined Z-model. -/
theorem characteristic_three_base_point :
    homogeneousNumerator (0:ZMod 3) 1=0 ∧
      homogeneousDenominator (0:ZMod 3) 1=0 ∧ (1:ZMod 3) ≠ 0 := by
  have h27 : (27:ZMod 3)=0 := by decide
  simp [homogeneousNumerator,homogeneousDenominator,h27]

end ThreeProjectiveJCertificates318
