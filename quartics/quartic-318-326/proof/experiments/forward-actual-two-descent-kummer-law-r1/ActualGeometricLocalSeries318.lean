module
public import ActualOriginalCompleteFourierCount318
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public section
noncomputable section
namespace ActualGeometricLocalSeries318
open Filter
open scoped BigOperators Topology
set_option maxHeartbeats 16000000

/-- Local Fourier layers are successive differences of the complete
frequency averages, with their genuine modulus-one initial term. -/
@[expose] def layers (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | n+1 => b (n+1)-b n

lemma actual_layer_partial_sum (b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), layers b i) = b n := by
  induction n with
  | zero => simp [layers]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [layers]
    ring

/-- Parity-dependent geometric convergence of the actual normalized
counts gives an ABSOLUTELY summable error, not merely a sequential limit. -/
theorem parity_error_summable (b : ℕ → ℝ) (S A B r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : ∀ n, b (2*n) = S+A*r^n)
    (ho : ∀ n, b (2*n+1) = S+B*r^n) :
    Summable (fun n => ‖b n-S‖) := by
  have hg : Summable (fun n : ℕ => r^n) := summable_geometric_of_lt_one hr0 hr1
  have hE : Summable (fun n : ℕ => ‖b (2*n)-S‖) := by
    simp_rw [he,add_sub_cancel_left,norm_mul,Real.norm_eq_abs,
      abs_pow,abs_of_nonneg hr0]
    exact hg.mul_left |A|
  have hO : Summable (fun n : ℕ => ‖b (2*n+1)-S‖) := by
    simp_rw [ho,add_sub_cancel_left,norm_mul,Real.norm_eq_abs,
      abs_pow,abs_of_nonneg hr0]
    exact hg.mul_left |B|
  exact hE.even_add_odd hO

theorem layers_summable_norm_of_error (b : ℕ → ℝ) (S : ℝ)
    (hb : Summable (fun n => ‖b n-S‖)) : Summable (fun n => ‖layers b n‖) := by
  have hshift : Summable (fun n : ℕ => ‖b (n+1)-S‖) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hdiff : Summable (fun n : ℕ => ‖b (n+1)-b n‖) := by
    apply (hshift.add hb).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    rw [show b (n+1)-b n = (b (n+1)-S)-(b n-S) by ring]
    exact norm_sub_le _ _
  apply (summable_nat_add_iff 1).mp
  simpa only [layers] using hdiff

/-- A genuine absolutely convergent local series whose sum is the
actual count limit. Sequential telescoping alone would be insufficient. -/
theorem actual_layers_hasSum (b : ℕ → ℝ) (S T : ℝ)
    (hb : Summable (fun n => ‖b n-S‖))
    (hlim : Tendsto b atTop (𝓝 T)) : HasSum (layers b) T := by
  have hs := layers_summable_norm_of_error b S hb
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  have hn : Tendsto (fun n : ℕ => n-1) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro k
    exact eventually_atTop.mpr ⟨k+1,fun n hn => by omega⟩
  apply (hlim.comp hn).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [←actual_layer_partial_sum b (n-1),Nat.sub_add_cancel hn]

end ActualGeometricLocalSeries318
