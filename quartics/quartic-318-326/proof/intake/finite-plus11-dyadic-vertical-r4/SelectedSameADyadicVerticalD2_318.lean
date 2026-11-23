module
public import SelectedActualSameAFiniteDlogRows318
public import FractionDerivation318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import all SelectedActualSameAFiniteDlogRows318

/-! The exact divided section pair at a reduced vertical component of the
original structural scheme. The coefficient ring here is not a ramified
height trait. The original functions and relative frame must be supplied by
the model; no calibrated twist signs, completed fields or height hypotheses
are required. -/
public section
noncomputable section

open scoped nonZeroDivisors

namespace SelectedSameADyadicVerticalD2_318

open SelectedActualSameAFiniteDlogRows318

private theorem irreducible_of_reduced_quotient {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (a : R) (ha : a ≠ 0) (hn : ¬IsUnit a)
    [IsReduced (R ⧸ Ideal.span ({a} : Set R))] : Irreducible a := by
  let I := Ideal.span ({a} : Set R)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hm : π^n ∈ I := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(u⁻¹) : R), ?_⟩
    calc
      π^n = ((u : R) * (↑(u⁻¹) : R)) * π^n := by rw [Units.mul_inv, one_mul]
      _ = ((u : R) * π^n) * (↑(u⁻¹) : R) := by ring
      _ = a * (↑(u⁻¹) : R) := by rw [he]
  have hnil : IsNilpotent (Ideal.Quotient.mk I π) :=
    ⟨n, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hm⟩
  have hmem : π ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (isNilpotent_iff_eq_zero.mp hnil)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨hn, ?_⟩
  intro x y hxy
  have hfac : π = x * (y * b) := by rw [hb, hxy, mul_assoc]
  rcases hπ.isUnit_or_isUnit hfac with hx | hy
  · exact Or.inl hx
  · exact Or.inr ((IsUnit.mul_iff.mp hy).1)

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

omit [CharZero K] in
private theorem kills_rat (D : Derivation ℤ K K) (q : ℚ) :
    D (algebraMap ℚ K q) = 0 := by
  have he : algebraMap ℚ K q =
      algebraMap ℤ K q.num / algebraMap ℤ K (q.den : ℤ) := by
    conv_lhs => rw [← q.num_div_den]
    rw [map_div₀, map_intCast, map_natCast]
    norm_num
  rw [he, D.leibniz_div, D.map_algebraMap, D.map_algebraMap]
  simp

variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- An actual relative cotangent frame gives an integral relative derivation,
which is then uniquely extended to the original structural function field. -/
@[expose] def fractionDerivative (frame : KaehlerDifferential ℤ R →ₗ[R] R) :
    Derivation ℤ K K :=
  FractionDerivation318.extend (K := K) (frame.compDer (KaehlerDifferential.D ℤ R))

omit [CharZero K] [Algebra ℚ K] [IsDiscreteValuationRing R] in
theorem fractionDerivative_apply (frame : KaehlerDifferential ℤ R →ₗ[R] R) (a : R) :
    fractionDerivative R frame (a : K) =
      (frame (KaehlerDifferential.D ℤ R a) : K) :=
  FractionDerivation318.extend_integral (K := K)
    (frame.compDer (KaehlerDifferential.D ℤ R)) a

private theorem rational_times_unit (hπ : Irreducible (2 : R)) (x : K) (hx : x ≠ 0) :
    ∃ q : ℚˣ, ∃ u : Rˣ, x = algebraMap ℚ K (q : ℚ) * ((u : R) : K) := by
  obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hsr : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.property
  have hs : ((s : R) : K) ≠ 0 := fun h => hsr (Subtype.ext h)
  change x * ((s : R) : K) = (a : K) at he
  have ha : a ≠ 0 := by
    intro h
    exact (mul_ne_zero hx hs) (he.trans (by simp [h]))
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hsr hπ
  let q : ℚˣ := Units.mk0 ((2 : ℚ)^m / (2 : ℚ)^n)
    (div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
  refine ⟨q, u / v, ?_⟩
  have hvK : ((v : R) : K) ≠ 0 := (v.isUnit.map R.subtype).ne_zero
  have vv : ((v : R) : K) * ((↑(v⁻¹) : R) : K) = 1 :=
    congrArg R.subtype v.mul_inv
  have vi : ((↑(v⁻¹) : R) : K) = ((v : R) : K)⁻¹ := by
    apply mul_left_cancel₀ hvK
    rw [vv, mul_inv_cancel₀ hvK]
  have hsEq : ((s : R) : K) = ((v : R) : K) * (2 : K)^n := by
    change R.subtype (s : R) = R.subtype (v : R) * (2 : K)^n
    simpa only [map_mul, map_pow, map_ofNat] using congrArg R.subtype hv
  have haEq : (a : K) = ((u : R) : K) * (2 : K)^m := by
    change R.subtype a = R.subtype (u : R) * (2 : K)^m
    simpa only [map_mul, map_pow, map_ofNat] using congrArg R.subtype hu
  rw [hsEq, haEq] at he
  change x = algebraMap ℚ K ((2 : ℚ)^m / (2 : ℚ)^n) *
    (((u : R) : K) * ((↑(v⁻¹) : R) : K))
  have h2 : (2 : K) ≠ 0 := by norm_num
  rw [map_div₀, map_pow, map_pow, map_ofNat, vi]
  have hd : x = (((u : R) : K) * (2 : K)^m) /
      (((v : R) : K) * (2 : K)^n) :=
    (eq_div_iff (mul_ne_zero hvK (pow_ne_zero _ h2))).2 he
  rw [hd, ← div_eq_mul_inv ((u : R) : K) ((v : R) : K), div_mul_div_comm,
    mul_comm ((u : R) : K) ((2 : K)^m),
    mul_comm ((v : R) : K) ((2 : K)^n)]

omit [CharZero K] [IsDiscreteValuationRing R] in
private theorem root_log_mem (frame : KaehlerDifferential ℤ R →ₗ[R] R)
    (x : K) (q : ℚˣ) (u : Rˣ) (hx : x = algebraMap ℚ K (q : ℚ) * ((u : R) : K)) :
    fractionDerivative R frame x / x ∈ R := by
  let D : Derivation ℤ K K := fractionDerivative R frame
  change D x / x ∈ R
  have hu : ((u : R) : K) ≠ 0 := (u.isUnit.map R.subtype).ne_zero
  have hq : algebraMap ℚ K (q : ℚ) ≠ 0 := by
    simpa only [map_zero] using (algebraMap ℚ K).injective.ne q.ne_zero
  have hi : ((u : R) : K) * ((↑(u⁻¹) : R) : K) = 1 := congrArg R.subtype u.mul_inv
  have hr : D x / x = D ((u : R) : K) * ((↑(u⁻¹) : R) : K) := by
    rw [hx, D.leibniz, kills_rat, smul_zero, add_zero, smul_eq_mul]
    apply (div_eq_iff (mul_ne_zero hq hu)).2
    calc
      _ = algebraMap ℚ K (q : ℚ) * D ((u : R) : K) *
          (((u : R) : K) * ((↑(u⁻¹) : R) : K)) := by rw [hi, mul_one]
      _ = _ := by ring
  rw [hr]
  change fractionDerivative R frame ((u : R) : K) * ((↑(u⁻¹) : R) : K) ∈ R
  rw [fractionDerivative_apply]
  exact R.mul_mem (frame (KaehlerDifferential.D ℤ R (u : R))).property (↑(u⁻¹) : R).property

private theorem log_rule (D : Derivation ℤ K K) (t x : K) (i : Fin 4) (c : ℚˣ)
    (hx : x ≠ 0) (hn : contact t i ≠ 0)
    (he : x^2 = algebraMap ℚ K (c : ℚ) * contact t i) :
    D t = 2 * contact t i * (D x / x) := by
  have hc : algebraMap ℚ K (c : ℚ) ≠ 0 := by
    simpa only [map_zero] using (algebraMap ℚ K).injective.ne c.ne_zero
  have hd := congrArg D he
  simp only [contact, pow_two, Derivation.leibniz, kills_rat, map_sub, sub_zero, smul_eq_mul] at hd
  have hD : D x / x = D t / (2 * contact t i) := by
    apply (div_eq_div_iff hx (mul_ne_zero (by norm_num) hn)).2
    apply mul_left_cancel₀ hc
    calc
      _ = (2 * D x) * (algebraMap ℚ K (c : ℚ) * contact t i) := by ring
      _ = (2 * D x) * x^2 := by rw [← he]
      _ = (x * D x + x * D x) * x := by ring
      _ = _ := by rw [hd]; ring
  rw [hD, mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hn)]

/-- The same two divided tensors have integral coefficients on every original
reduced dyadic structural DVR carrying the labelled generic functions.
Only the relative frame and the actual original field/root binding are
needed from geometry; the log coefficients themselves are constructed. -/
theorem coefficients_mem (h2 : ¬IsUnit (2 : R))
    [IsReduced (R ⧸ Ideal.span ({(2 : R)} : Set R))]
    (frame : KaehlerDifferential ℤ R →ₗ[R] R) (t : K)
    (roots : Fin 4 → K) (twists : Fin 4 → ℚˣ)
    (hn : ∀ i, contact t i ≠ 0)
    (he : ∀ i, (roots i)^2 = algebraMap ℚ K (twists i : ℚ) * contact t i) :
    let q := qcoeff t (fractionDerivative R frame t)
    ((25725/4 : K) * 32 * q ∈ R) ∧ ((25725/4 : K) * t * q ∈ R) := by
  have h2R : (2 : R) ≠ 0 := by
    intro h
    have hK := congrArg R.subtype h
    exact (by norm_num : (2 : K) ≠ 0) (by simpa only [map_ofNat, map_zero] using hK)
  have hπ := irreducible_of_reduced_quotient (2 : R) h2R h2
  have hr (i : Fin 4) : roots i ≠ 0 := by
    have hc : algebraMap ℚ K (twists i : ℚ) ≠ 0 := by
      simpa only [map_zero] using (algebraMap ℚ K).injective.ne (twists i).ne_zero
    have h := mul_ne_zero hc (hn i)
    intro hzero
    apply h
    rw [← he i, hzero, zero_pow (by decide : 2 ≠ 0)]
  let δ : Derivation ℤ K K := fractionDerivative R frame
  let d : Fin 4 → R := fun i =>
    ⟨δ (roots i) / roots i, by
      obtain ⟨q, u, h⟩ := rational_times_unit R hπ (roots i) (hr i)
      exact root_log_mem R frame (roots i) q u h⟩
  have hd (i : Fin 4) : δ t = 2 * contact t i * (d i : K) :=
    log_rule δ t (roots i) i (twists i) (hr i) (hn i) (he i)
  have hh := integral_pair R t (δ t) d hn hd
  exact ⟨hh.1 ▸ (row0 d).property, hh.2 ▸ (row1 d).property⟩

end SelectedSameADyadicVerticalD2_318
