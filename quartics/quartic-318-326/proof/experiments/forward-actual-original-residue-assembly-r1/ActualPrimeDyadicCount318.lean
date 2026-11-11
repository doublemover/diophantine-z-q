module
public import ActualOriginalEulerComparison318
public section
noncomputable section
namespace ActualPrimeDyadicCount318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def lower (N k : ℕ) : ℕ := N*2^k
@[expose] def block (N k : ℕ) : Finset ℕ :=
  (Finset.Ico (lower N k) (lower N (k+1))).filter Nat.Prime

lemma lower_pos (N : ℕ) (hN : 0<N) (k : ℕ) : 0<lower N k :=
  Nat.mul_pos hN (pow_pos (by norm_num) _)
lemma lower_base_le (N k : ℕ) : N≤lower N k := by
  have hh : 1≤(2:ℕ)^k := one_le_pow₀ (by norm_num)
  simpa only [mul_one] using Nat.mul_le_mul_left N hh
lemma lower_mono (N : ℕ) : Monotone (lower N) := by
  intro a b hab
  exact Nat.mul_le_mul_left N (pow_right_mono₀ (by norm_num : (1:ℕ)≤2) hab)

/-- Every actual dyadic prime block is bounded by Chebyshev theta,
with the true logN denominator retained before weighting the tail. -/
theorem actual_block_count (N : ℕ) (hN : 1<N) (k : ℕ) :
    ((block N k).card:ℝ)*Real.log (N:ℝ)≤Real.log 4*(lower N (k+1):ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlow (p : ℕ) (hp : p∈block N k) : Real.log (N:ℝ)≤Real.log (p:ℝ) := by
    have hlo := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hh : N≤p := (lower_base_le N k).trans hlo
    exact Real.log_le_log hn (by exact_mod_cast hh)
  have hs : ((block N k).card:ℝ)*Real.log (N:ℝ)≤∑p∈block N k,Real.log (p:ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hlow
  have hsub : block N k⊆(Finset.Ioc 0 (lower N (k+1))).filter Nat.Prime := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨hh.2.pos,(Finset.mem_Ico.mp hh.1).2.le⟩,hh.2⟩
  have htheta : (∑p∈block N k,Real.log (p:ℝ))≤Chebyshev.theta (lower N (k+1):ℝ) := by
    rw [Chebyshev.theta,Nat.floor_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
  exact hs.trans (htheta.trans (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)))

lemma actual_block_card_bound (N : ℕ) (hN : 1<N) (k : ℕ) :
    ((block N k).card:ℝ)≤Real.log 4*(lower N (k+1):ℝ)/Real.log (N:ℝ) := by
  have hl : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  exact (le_div_iff₀ hl).mpr (actual_block_count N hN k)

end ActualPrimeDyadicCount318
