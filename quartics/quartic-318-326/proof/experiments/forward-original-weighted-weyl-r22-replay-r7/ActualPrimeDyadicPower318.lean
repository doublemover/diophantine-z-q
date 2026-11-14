module
public import ActualPrimeDyadicCount318
public section
noncomputable section
namespace ActualPrimeDyadicPower318
open scoped BigOperators
open ActualPrimeDyadicCount318
set_option maxHeartbeats 16000000

@[expose] def ratio (δ : ℝ) : ℝ := (2:ℝ)^(-δ)
@[expose] def amplitude (N : ℕ) (δ : ℝ) : ℝ :=
  2*Real.log 4*(N:ℝ)^(-δ)/Real.log (N:ℝ)
@[expose] def primeWeight (δ : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then (p:ℝ)^(-(1+δ)) else 0
lemma primeWeight_nonneg (δ : ℝ) (p : ℕ) : 0≤primeWeight δ p := by
  unfold primeWeight
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · rfl
lemma cancel_linear_power (x : ℝ) (hx : 0<x) (δ : ℝ) :
    x*x^(-(1+δ))=x^(-δ) := by
  calc
    _ = x^(1:ℝ)*x^(-(1+δ)) := by rw [Real.rpow_one]
    _ = x^((1:ℝ)+(-(1+δ))) := (Real.rpow_add hx _ _).symm
    _ = x^(-δ) := by congr 1;ring
lemma lower_power (N k : ℕ) (δ : ℝ) :
    (lower N k:ℝ)^(-δ)=(N:ℝ)^(-δ)*ratio δ^k := by
  simp only [lower,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
    ←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
  rfl

/-- Actual prime block mass, not an all-integer tail. The logN gain
from the true Chebyshev prime count survives in the amplitude. -/
theorem actual_block_power (N : ℕ) (hN : 1<N) (δ : ℝ) (hδ : 0<δ) (k : ℕ) :
    (∑p∈Finset.Ico (lower N k) (lower N (k+1)),primeWeight δ p)≤amplitude N δ*ratio δ^k := by
  have hL : (0:ℝ)<lower N k := by exact_mod_cast lower_pos N (by omega) k
  have hw (p : ℕ) (hp : p∈block N k) :
      (p:ℝ)^(-(1+δ))≤(lower N k:ℝ)^(-(1+δ)) :=
    Real.rpow_le_rpow_of_nonpos hL
      (by exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1) (by linarith)
  have hs := Finset.sum_le_sum hw
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hc := mul_le_mul_of_nonneg_right (actual_block_card_bound N hN k)
    (Real.rpow_nonneg (Nat.cast_nonneg (lower N k)) (-(1+δ)))
  have hU : (lower N (k+1):ℝ)=2*(lower N k:ℝ) := by
    simp only [lower,pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  have he : (Real.log 4*(lower N (k+1):ℝ)/Real.log (N:ℝ))*
      (lower N k:ℝ)^(-(1+δ))=amplitude N δ*ratio δ^k := by
    rw [hU]
    calc
      _ = (2*Real.log 4/Real.log (N:ℝ))*
          ((lower N k:ℝ)*(lower N k:ℝ)^(-(1+δ))) := by ring
      _ = _ := by rw [cancel_linear_power _ hL,lower_power];unfold amplitude;ring
  have hsum : (∑p∈Finset.Ico (lower N k) (lower N (k+1)),primeWeight δ p)=
      ∑p∈block N k,(p:ℝ)^(-(1+δ)) := by
    simp only [block,Finset.sum_filter,primeWeight]
  rw [hsum]
  exact hs.trans (hc.trans_eq he)

lemma ratio_bounds (δ : ℝ) (hδ : 0<δ) : 0≤ratio δ ∧ ratio δ<1 :=
  ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2) (by linarith)⟩
lemma amplitude_nonneg (N : ℕ) (hN : 1<N) (δ : ℝ) : 0≤amplitude N δ := by
  have hl := (Real.log_pos (by exact_mod_cast hN : (1:ℝ)<N)).le
  have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  have hp := Real.rpow_nonneg (Nat.cast_nonneg N) (-δ)
  unfold amplitude
  positivity

end ActualPrimeDyadicPower318
