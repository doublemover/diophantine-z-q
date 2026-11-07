module
public import CanonicalLimit
public section
noncomputable section
open Filter Topology CanonicalLimit
namespace CanonicalQuadratic
set_option maxHeartbeats 0
variable {G : Type*} [AddCommGroup G]

lemma raw_parallelogram {h:G→ℝ} {L U C:ℝ} (d:Bounds h L U)
    (hp : ∀P Q, |h (P+Q)+h (P-Q)-2*(h P+h Q)|≤C) (P Q:G) :
    raw h (P+Q)+raw h (P-Q)=2*(raw h P+raw h Q) := by
  let f (n:ℕ) := CanonicalLimit.seq h (P+Q) n+CanonicalLimit.seq h (P-Q) n-2*(CanonicalLimit.seq h P n+CanonicalLimit.seq h Q n)
  have hbound (n:ℕ) : |f n|≤C*(1/4:ℝ)^n := by
    have hh := mul_le_mul_of_nonneg_left (hp ((2^n:ℕ) • P) ((2^n:ℕ) • Q))
      (by positivity : (0:ℝ)≤(1/4:ℝ)^n)
    have he : f n=(1/4:ℝ)^n * (h ((2^n:ℕ) • P+(2^n:ℕ) • Q)+h ((2^n:ℕ) • P-(2^n:ℕ) • Q)-
        2*(h ((2^n:ℕ) • P)+h ((2^n:ℕ) • Q))) := by
      simp only [f,CanonicalLimit.seq,nsmul_add,nsmul_sub]
      ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(1/4:ℝ)^n)]
    nlinarith
  have ht0 : Tendsto (fun n:ℕ => C*(1/4:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4)
      (by norm_num : (1/4:ℝ)<1)).const_mul C
  have hz : Tendsto f atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun n => -(C*(1/4:ℝ)^n))
      (h:=fun n => C*(1/4:ℝ)^n) (by simpa using ht0.neg) ht0
    · intro n; exact (abs_le.mp (hbound n)).1
    · intro n; exact (abs_le.mp (hbound n)).2
  have ht : Tendsto f atTop (𝓝 (raw h (P+Q)+raw h (P-Q)-2*(raw h P+raw h Q))) :=
    ((tendsto_raw d (P+Q)).add (tendsto_raw d (P-Q))).sub
      (((tendsto_raw d P).add (tendsto_raw d Q)).const_mul 2)
  have he := tendsto_nhds_unique ht hz
  linarith

lemma quadratic_neg {q:G→ℝ} (hz:q 0=0)
    (hp : ∀P Q,q (P+Q)+q (P-Q)=2*(q P+q Q)) (P:G) : q (-P)=q P := by
  have hh := hp 0 P
  simp only [zero_add,zero_sub,hz] at hh
  linarith

lemma quadratic_nsmul {q:G→ℝ} (hz:q 0=0)
    (hp : ∀P Q,q (P+Q)+q (P-Q)=2*(q P+q Q)) (P:G) (n:ℕ) : q (n • P)=(n:ℝ)^2*q P := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hz]
  | one => simp
  | more n h0 h1 =>
    have hh := hp ((n+1) • P) P
    have ha : (n+1) • P+P=(n+2) • P := by simp [add_nsmul,add_assoc,two_nsmul]
    have hs : (n+1) • P-P=n • P := by simp [add_nsmul]
    rw [ha,hs,h0,h1] at hh
    push_cast at hh ⊢
    nlinarith

lemma quadratic_zsmul {q:G→ℝ} (hz:q 0=0)
    (hp : ∀P Q,q (P+Q)+q (P-Q)=2*(q P+q Q)) (P:G) (n:ℤ) : q (n • P)=(n:ℝ)^2*q P := by
  cases n with
  | ofNat n => simpa using quadratic_nsmul hz hp P n
  | negSucc n =>
    have hn := quadratic_nsmul hz hp P (n+1)
    have he : (Int.negSucc n) • P= -((n+1) • P) := by
      have he' : (Int.negSucc n)= -((n+1:ℕ):ℤ) := by omega
      rw [he',neg_smul,natCast_zsmul]
    rw [he,quadratic_neg hz hp]
    rw [hn]
    push_cast
    ring

lemma raw_zsmul {h:G→ℝ} {L U C:ℝ} (d:Bounds h L U) (hz:h 0=0)
    (hp : ∀P Q, |h (P+Q)+h (P-Q)-2*(h P+h Q)|≤C) (P:G) (n:ℤ) :
    raw h (n • P)=(n:ℝ)^2*raw h P :=
  quadratic_zsmul (raw_zero d hz) (raw_parallelogram d hp) P n

#print axioms raw_parallelogram
#print axioms quadratic_neg
#print axioms quadratic_nsmul
#print axioms quadratic_zsmul
#print axioms raw_zsmul
end CanonicalQuadratic
