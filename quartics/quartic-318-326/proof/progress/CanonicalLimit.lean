module
public import Mathlib.Analysis.SpecificLimits.Basic
public section
noncomputable section
open Filter Topology
namespace CanonicalLimit
set_option maxHeartbeats 0
variable {G : Type*} [AddCommGroup G]

@[expose] def seq (h : G→ℝ) (P : G) (n : ℕ) : ℝ := (1/4:ℝ)^n*h ((2^n:ℕ) • P)
@[expose] def raw (h : G→ℝ) (P : G) : ℝ := Filter.limUnder atTop (seq h P)
@[expose] def height (h : G→ℝ) (P : G) : ℝ := raw h P/2

structure Bounds (h : G→ℝ) (L U : ℝ) : Prop where
  lower_nonneg : 0≤L
  upper_nonneg : 0≤U
  lower : ∀P, 4*h P-L≤h ((2:ℕ) • P)
  upper : ∀P, h ((2:ℕ) • P)≤4*h P+U

lemma orbit_succ (P:G) (n:ℕ) : (2^(n+1):ℕ) • P=(2:ℕ) • ((2^n:ℕ) • P) := by
  rw [smul_smul,pow_succ,mul_comm]

lemma seq_succ (h:G→ℝ) (P:G) (n:ℕ) :
    seq h P (n+1)=(1/4:ℝ)^(n+1)*h ((2:ℕ) • ((2^n:ℕ) • P)) := by rw [seq,orbit_succ]

lemma step_bounds {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) (n:ℕ) :
    seq h P n-L/4*(1/4:ℝ)^n≤seq h P (n+1) ∧
    seq h P (n+1)≤seq h P n+U/4*(1/4:ℝ)^n := by
  have hl := mul_le_mul_of_nonneg_left (d.lower ((2^n:ℕ) • P)) (by positivity : (0:ℝ)≤(1/4:ℝ)^(n+1))
  have hu := mul_le_mul_of_nonneg_left (d.upper ((2^n:ℕ) • P)) (by positivity : (0:ℝ)≤(1/4:ℝ)^(n+1))
  rw [seq_succ,seq,pow_succ]
  rw [pow_succ] at hl hu
  constructor <;> nlinarith

lemma seq_cauchy {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) : CauchySeq (seq h P) := by
  apply cauchySeq_of_le_geometric (1/4) (max L U/4) (by norm_num)
  intro n
  rw [Real.dist_eq,abs_sub_comm,abs_le]
  have hs := step_bounds d P n
  have hl := mul_le_mul_of_nonneg_right (le_max_left L U) (by positivity : (0:ℝ)≤(1/4:ℝ)^n)
  have hu := mul_le_mul_of_nonneg_right (le_max_right L U) (by positivity : (0:ℝ)≤(1/4:ℝ)^n)
  constructor <;> nlinarith

lemma tendsto_raw {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) :
    Tendsto (seq h P) atTop (𝓝 (raw h P)) := (seq_cauchy d P).tendsto_limUnder

lemma seq_bounds {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) (n:ℕ) :
    h P-L/3*(1-(1/4:ℝ)^n)≤seq h P n ∧
    seq h P n≤h P+U/3*(1-(1/4:ℝ)^n) := by
  induction n with
  | zero => simp [seq]
  | succ n ih =>
    have hs := step_bounds d P n
    rw [pow_succ]
    constructor <;> nlinarith [ih.1,ih.2,hs.1,hs.2]

lemma raw_bounds {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) :
    h P-L/3≤raw h P ∧ raw h P≤h P+U/3 := by
  have ht := tendsto_raw d P
  constructor
  · apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro n
    have hh := (seq_bounds d P n).1
    nlinarith [mul_nonneg d.lower_nonneg (show (0:ℝ)≤(1/4:ℝ)^n by positivity)]
  · apply le_of_tendsto ht
    apply Eventually.of_forall
    intro n
    have hh := (seq_bounds d P n).2
    nlinarith [mul_nonneg d.upper_nonneg (show (0:ℝ)≤(1/4:ℝ)^n by positivity)]

lemma raw_nonneg {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (hn : ∀P,0≤h P) (P:G) : 0≤raw h P := by
  apply ge_of_tendsto (tendsto_raw d P)
  exact Eventually.of_forall (fun n => mul_nonneg (by positivity) (hn _))

lemma raw_zero {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (hz:h 0=0) : raw h 0=0 := by
  apply tendsto_nhds_unique (tendsto_raw d 0)
  have he : seq h 0=(fun _ : ℕ => (0:ℝ)) := by funext n; simp [seq,hz]
  rw [he]
  exact tendsto_const_nhds

lemma raw_double {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P:G) : raw h ((2:ℕ) • P)=4*raw h P := by
  have ht := (tendsto_raw d P).comp (tendsto_add_atTop_nat 1)
  have he (n:ℕ) : seq h ((2:ℕ) • P) n=4*seq h P (n+1) := by
    simp only [seq,pow_succ,smul_smul]
    ring
  have ht' := ht.const_mul 4
  apply tendsto_nhds_unique (tendsto_raw d ((2:ℕ) • P))
  exact ht'.congr' (Eventually.of_forall (fun n => (he n).symm))

lemma raw_two_torsion {h:G→ℝ} {L U:ℝ} (d:Bounds h L U) (P T:G) (hT:T+T=0) :
    raw h (P+T)=raw h P := by
  have he : (2:ℕ) • (P+T)=(2:ℕ) • P := by simp only [nsmul_add,two_nsmul,hT,add_zero]
  have hh := congrArg (raw h) he
  rw [raw_double d,raw_double d] at hh
  linarith

#print axioms seq_cauchy
#print axioms tendsto_raw
#print axioms seq_bounds
#print axioms raw_bounds
#print axioms raw_nonneg
#print axioms raw_zero
#print axioms raw_double
#print axioms raw_two_torsion
end CanonicalLimit
