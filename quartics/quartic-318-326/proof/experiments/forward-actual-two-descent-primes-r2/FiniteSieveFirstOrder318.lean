module
public import OriginalSieveResidueDensity318
public section
noncomputable section
namespace FiniteSieveFirstOrder318
open FiniteSieveDensity318
set_option maxHeartbeats 1000000

@[expose] def rawDensity (q k e : ℚ) : ℚ :=
  ((q-1)*(q-e)*(2*(q+(q-1)*e)+(k-2)*(q-e))+(q+(q-1)*e)^2-1)/(q^4-1)
@[expose] def remainderNumerator (q k e : ℚ) : ℚ :=
  (2*e+1)*k*q^2+2*e*(q+1)+k
@[expose] def remainderDenominator (q : ℚ) : ℚ := q*(q+1)*(q^2+1)

lemma denominator_positive (q : ℚ) (hq : 1<q) : 0<remainderDenominator q := by
  have hq0 : 0<q := by linarith
  dsimp [remainderDenominator]
  positivity

lemma quartic_ne (q : ℚ) (hq : 1<q) : q^4-1≠0 := by
  have hq2 : 1<q^2 := by nlinarith
  nlinarith [sq_nonneg (q^2-1)]

/-- Exact lower-order term of the actual local-density formula. -/
theorem exact_remainder (q k e : ℚ) (hq : 1<q) (he : e=1 ∨ e= -1) :
    rawDensity q k e-(k+2*e)/q=
      -remainderNumerator q k e/remainderDenominator q := by
  have hq0 : q≠0 := by linarith
  have hq1 : q+1≠0 := by linarith
  have hq2 : q^2+1≠0 := by positivity
  have hq4 := quartic_ne q hq
  rcases he with rfl|rfl <;> dsimp [rawDensity,remainderNumerator,remainderDenominator]
  all_goals field_simp [hq0,hq1,hq2,hq4]
  all_goals ring

lemma numerator_bound (q k e : ℚ) (hq : 1<q) (hk : 0≤k) (he : e=1 ∨ e= -1) :
    |remainderNumerator q k e|≤4*(k+1)*q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := by nlinarith
  have hkb : k≤k*q^2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq2 hk
  have hgeom : 2*q+2≤4*q^2 := by nlinarith
  have hkq : 0≤k*q^2 := mul_nonneg hk (sq_nonneg q)
  rcases he with rfl|rfl
  · have hn : 0≤remainderNumerator q k 1 := by dsimp [remainderNumerator]; positivity
    rw [abs_of_nonneg hn]
    dsimp [remainderNumerator]
    nlinarith
  · have hn : remainderNumerator q k (-1)≤0 := by dsimp [remainderNumerator]; nlinarith
    rw [abs_of_nonpos hn]
    dsimp [remainderNumerator]
    nlinarith

lemma denominator_lower (q : ℚ) (hq : 1<q) : q^4≤remainderDenominator q := by
  have he : remainderDenominator q=q^4+q^3+q^2+q := by dsimp [remainderDenominator]; ring
  rw [he]
  have hq0 : 0≤q := by linarith
  have hq3 : 0≤q^3 := pow_nonneg hq0 3
  linarith [sq_nonneg q]

/-- Explicit uniform error bound, stronger than an unspecified O_k(q^-2). -/
theorem rational_error (q k e : ℚ) (hq : 1<q) (hk : 0≤k) (he : e=1 ∨ e= -1) :
    |rawDensity q k e-(k+2*e)/q|≤4*(k+1)/q^2 := by
  rw [exact_remainder q k e hq he,abs_div,abs_neg,
    abs_of_pos (denominator_positive q hq)]
  have hq2 : 0<q^2 := sq_pos_of_pos (by linarith)
  apply (div_le_div_iff₀ (denominator_positive q hq) hq2).mpr
  calc
    |remainderNumerator q k e|*q^2≤(4*(k+1)*q^2)*q^2 :=
      mul_le_mul_of_nonneg_right (numerator_bound q k e hq hk he) (le_of_lt hq2)
    _ = 4*(k+1)*q^4 := by ring
    _ ≤ 4*(k+1)*remainderDenominator q :=
      mul_le_mul_of_nonneg_left (denominator_lower q hq) (by positivity)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual original local density has first-order coefficient k+2chi(-1)
and an explicit4(k+1)/q² error, with no supplied analytic estimate. -/
theorem actual_error (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) :
    |density κ γ i₀-((Fintype.card ι:ℚ)+2*(quadraticChar F (-1:F):ℚ))/(Fintype.card F:ℚ)|≤
      4*((Fintype.card ι:ℚ)+1)/(Fintype.card F:ℚ)^2 := by
  have hν : (nuZero (F:=F):ℚ)=(Fintype.card F:ℚ)+
      ((Fintype.card F:ℚ)-1)*(quadraticChar F (-1:F):ℚ) := by
    simp only [nuZero,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,Int.cast_one]
  have hn : (nonzeroCount (F:=F):ℚ)=(Fintype.card F:ℚ)-(quadraticChar F (-1:F):ℚ) := by
    simp only [nonzeroCount,Int.cast_sub,Int.cast_natCast]
  have hq : (1:ℚ)<Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α:=F))
  have he : (quadraticChar F (-1:F):ℚ)=1 ∨ (quadraticChar F (-1:F):ℚ)= -1 := by
    exact_mod_cast (quadraticChar_dichotomy (show (-1:F)≠0 from neg_ne_zero.mpr one_ne_zero))
  rw [density_formula hF h2 κ hκ γ hγ i₀ i₁ h0 h1,hν,hn]
  simpa only [rawDensity] using rational_error (Fintype.card F:ℚ) (Fintype.card ι:ℚ)
    (quadraticChar F (-1:F):ℚ) hq (Nat.cast_nonneg _) he

end FiniteSieveFirstOrder318
