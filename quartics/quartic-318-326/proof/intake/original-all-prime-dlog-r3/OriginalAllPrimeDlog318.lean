module
public import SelectedSameADyadicVerticalD2_318
import all SelectedActualSameAFiniteDlogRows318

/-! BOTH sharp coefficients on every reduced vertical component, not only at 2.
The four square classes have arbitrary nonzero rational twists; no elliptic
curve, constant extension, or known square roots are required at the selected
closed mark. The roots below live in the ORIGINAL structural function field. -/
public section
noncomputable section

namespace OriginalAllPrimeDlog318
open IsDiscreteValuationRing
open SelectedActualSameAFiniteDlogRows318 SelectedSameADyadicVerticalD2_318

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


variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]

omit [CharZero K] [Algebra ℚ K] in
/-- Actual integrity of a differential frame, hence EACH logarithmic
coefficient on the unramified structural DVR, for an arbitrary base
uniformizer killed by the derivation. In particular the base prime may
also be odd. -/
theorem integral_dlog (frame : KaehlerDifferential ℤ R →ₗ[R] R)
    (π : R) (hirr : Irreducible π) (hπ : fractionDerivative R frame (π : K) = 0) (x : K) :
    fractionDerivative R frame x / x ∈ R := by
  let D := fractionDerivative R frame
  change D x / x ∈ R
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, u, hu⟩ := exists_units_eq_smul_zpow_of_irreducible hirr hx
  let du : R := frame (KaehlerDifferential.D ℤ R (u : R))
  have hdu : D (algebraMap R K (u : R)) = algebraMap R K du :=
    fractionDerivative_apply R frame (u : R)
  have hπalgebra : D (algebraMap R K π) = 0 := hπ
  have hp0 : D ((algebraMap R K π)^n) = 0 := by
    rw [D.leibniz_zpow, hπalgebra]
    simp
  have hunit : algebraMap R K (↑(u⁻¹) : R) * algebraMap R K (u : R) = 1 := by
    rw [←map_mul]
    simp
  have hmul : D x = algebraMap R K (du * (↑(u⁻¹) : R)) * x := by
    simp only [Units.smul_def, Algebra.smul_def] at hu
    rw [hu, D.leibniz, hp0, smul_zero, zero_add, hdu, smul_eq_mul, map_mul]
    calc
      (algebraMap R K π)^n * algebraMap R K du =
          algebraMap R K du * ((algebraMap R K (↑(u⁻¹) : R) *
            algebraMap R K (u : R)) * (algebraMap R K π)^n) := by rw [hunit]; ring
      _ = _ := by ring
  rw [hmul, mul_div_cancel_right₀ _ hx]
  exact (du * (↑(u⁻¹) : R)).property

/-- All-prime original model reading. The actual coefficients are given as
integer quadratic polynomials in the four logarithmic derivatives. -/
theorem sharp_sections_at_vertical (p : ℕ) (hp : p ≠ 0) (hnunit : ¬IsUnit (p : R))
    [IsReduced (R ⧸ Ideal.span ({(p : R)} : Set R))]
    (frame : KaehlerDifferential ℤ R →ₗ[R] R) (t : K)
    (roots : Fin 4 → K) (twists : Fin 4 → ℚˣ)
    (hn : ∀ i, contact t i ≠ 0)
    (he : ∀ i, (roots i)^2 = algebraMap ℚ K (twists i : ℚ) * contact t i) :
    ∃ d : Fin 4 → R,
      (∀ i, (d i : K)=fractionDerivative R frame (roots i)/(roots i)) ∧
      ((row0 d : R) : K)=(25725/4:K)*32*qcoeff t (fractionDerivative R frame t) ∧
      ((row1 d : R) : K)=(25725/4:K)*t*qcoeff t (fractionDerivative R frame t) := by
  have pnz : (p : R) ≠ 0 := by
    intro h
    have hz := congrArg R.subtype h
    have hK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
    exact hK (by simpa only [map_natCast,map_zero] using hz)
  have hirr := irreducible_of_reduced_quotient (p : R) pnz hnunit
  let D := fractionDerivative R frame
  have hπ : D ((p:R):K)=0 := by
    change D (R.subtype (p:R))=0
    rw [map_natCast,D.map_natCast]
  let d : Fin 4 → R := fun i => ⟨D (roots i)/(roots i), integral_dlog R frame (p:R) hirr hπ _⟩
  have hr (i : Fin 4) : roots i ≠ 0 := by
    have hc := (algebraMap ℚ K).injective.ne (twists i).ne_zero
    have hq : algebraMap ℚ K (twists i : ℚ) ≠ 0 := by simpa only [map_zero] using hc
    intro h
    exact mul_ne_zero hq (hn i) (by simpa only [h,zero_pow (by decide : 2 ≠ 0)] using (he i).symm)
  have hlog (i : Fin 4) : D t=2*contact t i*(d i : K) :=
    log_rule D t (roots i) i (twists i) (hr i) (hn i) (he i)
  exact ⟨d,fun _ => rfl,integral_pair R t (D t) d hn hlog⟩

end OriginalAllPrimeDlog318
