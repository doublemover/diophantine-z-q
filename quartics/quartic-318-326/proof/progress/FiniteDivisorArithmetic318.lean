module
public import RationalAbsoluteHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public section
noncomputable section
namespace FiniteDivisorArithmetic318

/-- The actual sum of finite prime valuations weighted by log p. -/
@[expose] def primeLog (n:ℕ) : ℝ := n.factorization.sum (fun p e => e*Real.log p)

 theorem primeLog_eq_log (n:ℕ) : primeLog n=Real.log n :=
  (Real.log_nat_eq_sum_factorization n).symm

/-- The rational horizontal finite-contact sum for0,1,infinity. -/
@[expose] def horizontalContact (q:ℚ) : ℝ :=
  primeLog q.num.natAbs+primeLog q.den+primeLog (q.num-(q.den:ℤ)).natAbs

 theorem horizontalContact_eq (q:ℚ) : horizontalContact q=
    Real.log |(q.num:ℝ)|+Real.log (q.den:ℝ)+Real.log |(q.num:ℝ)-(q.den:ℝ)| := by
  simp only [horizontalContact,primeLog_eq_log,Nat.cast_natAbs,Int.cast_abs,Int.cast_sub,Int.cast_natCast]

/-- The no-extra-constant bound requires the positive unit interval. This is
exactly the source's selected reciprocal parameter, not an arbitrary rational. -/
theorem horizontal_contact_bound (q:ℚ) (hq0:0<q) (hq1:q<1) :
    horizontalContact q≤3*NumberField.absLogHeight₁ q := by
  have hn:0<q.num := by simpa using (Rat.lt_iff 0 q).mp hq0
  have hnd:q.num<(q.den:ℤ) := by simpa using (Rat.lt_iff q 1).mp hq1
  have hnR:(0:ℝ)<q.num := by exact_mod_cast hn
  have hdR:(0:ℝ)<q.den := by exact_mod_cast q.den_pos
  have hndR:(q.num:ℝ)<q.den := by exact_mod_cast hnd
  have hdiff : |(q.num:ℝ)-(q.den:ℝ)|=(q.den:ℝ)-(q.num:ℝ) := by
    rw [abs_of_neg (by linarith)]
    ring
  have hlogn:=Real.log_le_log hnR hndR.le
  have hlogdiff:=Real.log_le_log (show (0:ℝ)<q.den-(q.num:ℝ) by linarith)
    (show (q.den:ℝ)-(q.num:ℝ)≤q.den by linarith)
  have hheight:NumberField.absLogHeight₁ q=Real.log (q.den:ℝ) := by
    have h:=RationalAbsoluteHeight.absLogHeight_ratCast ℚ q
    simp only [Rat.cast_id,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs] at h
    rw [abs_of_pos hnR,max_eq_right hndR.le] at h
    exact h
  rw [horizontalContact_eq,abs_of_pos hnR,hdiff,hheight]
  linarith only [hlogn,hlogdiff]

/-- Every reciprocal selected by the source lies in the range where the
horizontal intersection bound has no additive log2 loss. -/
theorem reciprocal_horizontal_bound (m:ℕ) (hm:2≤m) :
    horizontalContact (1/(m:ℚ))≤3*NumberField.absLogHeight₁ (1/(m:ℚ)) := by
  apply horizontal_contact_bound
  · positivity
  · exact (div_lt_one (by exact_mod_cast (show 0<m by omega))).mpr (by exact_mod_cast hm)

/-- The exact vertical floor-log sum. It does not introduce a factor equal
to the covering degree. -/
theorem vertical_log_bound (S:Finset ℕ) (hp:∀p∈S,Nat.Prime p) (d:ℕ) (hd:0<d) :
    (∑p∈S,(⌊Real.log d/Real.log p⌋₊:ℝ)*Real.log p)≤S.card*Real.log d := by
  have hdlog:0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  calc
    (∑p∈S,(⌊Real.log d/Real.log p⌋₊:ℝ)*Real.log p)≤∑p∈S,Real.log (d:ℝ) := by
      apply Finset.sum_le_sum
      intro p hpS
      have hpR:(1:ℝ)<p := by exact_mod_cast (hp p hpS).one_lt
      have hplog:0<Real.log (p:ℝ) := Real.log_pos hpR
      have hfloor:=Nat.floor_le (div_nonneg hdlog hplog.le)
      have hh:=mul_le_mul_of_nonneg_right hfloor hplog.le
      simpa only [div_mul_cancel₀ _ hplog.ne'] using hh
    _=S.card*Real.log d := by simp

/-- Arithmetic part of the source's direct finite-divisor estimate. -/
theorem finite_contact_budget (q:ℚ) (hq0:0<q) (hq1:q<1)
    (S:Finset ℕ) (hp:∀p∈S,Nat.Prime p) (d:ℕ) (hd:0<d) :
    horizontalContact q+2*(∑p∈S,(⌊Real.log d/Real.log p⌋₊:ℝ)*Real.log p)≤
      3*NumberField.absLogHeight₁ q+2*S.card*Real.log d := by
  have hhor:=horizontal_contact_bound q hq0 hq1
  have hvert:=vertical_log_bound S hp d hd
  linarith only [hhor,hvert]

/-- The interval qualification is essential: the unrestricted no-constant
claim would already fail at the nonbranching rational value−1. -/
theorem negative_one_requires_qualification :
    3*NumberField.absLogHeight₁ (-1:ℚ)<horizontalContact (-1:ℚ) := by
  have hh:NumberField.absLogHeight₁ (-1:ℚ)=0 := by
    simpa using RationalAbsoluteHeight.absLogHeight_ratCast ℚ (-1)
  rw [hh,horizontalContact_eq]
  norm_num
  exact Real.log_pos (by norm_num)

end FiniteDivisorArithmetic318
