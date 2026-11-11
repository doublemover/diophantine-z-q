module
public import ActualFullLocalDensityRecurrence318
public section
noncomputable section
namespace ActualLocalVolumeClosedForm318
open ActualFullLocalDensityRecurrence318
set_option maxHeartbeats 24000000

@[expose] def ratio (p : ℕ) : ℚ := 1/(p:ℚ)^3
@[expose] def localFactor (p : ℕ) : ℚ := (1-1/(p:ℚ)^4)/(1-ratio p)

lemma ratio_lt_one (p : ℕ) (hp : p.Prime) : ratio p<1 := by
  have hp1 : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have hp2 : (1:ℚ)<(p:ℚ)^2 := by nlinarith [sq_nonneg ((p:ℚ)-1)]
  have hp3 : (1:ℚ)<(p:ℚ)^3 := by
    have hh := mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hp2)
    nlinarith [hh]
  exact (div_lt_one (by positivity : (0:ℚ)<(p:ℚ)^3)).mpr hp3
lemma local_fixed_point (p : ℕ) (hp : p.Prime) :
    1-1/(p:ℚ)^4+ratio p*localFactor p=localFactor p := by
  have hd : 1-ratio p≠0 := ne_of_gt (sub_pos.mpr (ratio_lt_one p hp))
  unfold localFactor
  field_simp [hd]
  <;> ring

lemma volume_zero (κ : ℤ) (p : ℕ) : volume κ p 0=1 := by
  simp only [volume,actual_level_zero,mul_zero,pow_zero,Nat.cast_one,div_one]
lemma volume_one (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) : volume κ p 1=1 := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  simp only [volume,actual_level_one κ p hp hp2 hκ,mul_one,Nat.cast_pow]
  exact div_self (pow_ne_zero 4 hp0)

/-- BOTH parity subsequences of the actual original count have this
exact formula. The initial values are constructed residue counts. -/
theorem actual_even_odd_formula (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    volume κ p (2*e)=localFactor p+(1-localFactor p)*ratio p^e ∧
    volume κ p (2*e+1)=localFactor p+(1-localFactor p)*ratio p^e := by
  have hstep (n : ℕ) : volume κ p (n+2)=1-1/(p:ℚ)^4+ratio p*volume κ p n := by
    rw [actual_whole_volume_recurrence κ p hp hp2 hκ n]
    simp only [ratio,div_eq_mul_inv,one_mul,mul_comm]
  induction e with
  | zero =>
    rw [mul_zero,zero_add,volume_zero,volume_one κ p hp hp2 hκ,pow_zero]
    constructor <;> ring
  | succ e ih =>
    have hE : 2*(e+1)=2*e+2 := by omega
    have hO : 2*(e+1)+1=(2*e+1)+2 := by omega
    have hO' : 2*e+2+1=(2*e+1)+2 := by omega
    simp only [hE,hO']
    rw [hstep,hstep,ih.1,ih.2,pow_succ (ratio p) e]
    have hf := local_fixed_point p hp
    constructor <;> nlinarith [hf]

/-- A single exact formula for EVERY finite original residue level. -/
theorem actual_full_volume_formula (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (n : ℕ) :
    volume κ p n=localFactor p+(1-localFactor p)*ratio p^(n/2) := by
  have hh := actual_even_odd_formula κ p hp hp2 hκ (n/2)
  have hc : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hc with he|ho
  · exact (congrArg (volume κ p) he).trans hh.1
  · exact (congrArg (volume κ p) ho).trans hh.2

end ActualLocalVolumeClosedForm318
