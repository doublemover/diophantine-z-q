module
public import ActualTZOrdinaryBoundaryScalar318
public import ActualTZShortStripPower318
public section
noncomputable section
namespace ActualTZOrdinaryBoundaryDecay318
open Filter
open scoped Topology
open ActualTZOrdinaryBoundaryScalar318 ActualTZShortStripPower318

@[expose] def remainder (k : ℕ) (ρ B Q : ℝ) (n : ℝ) : ℝ :=
  (Q+1)*(envelope k (n^ρ) B*short n)+Q*short n

/-- Actual boundary, interval, and center-deficit allowances
collect into one locally uniform fixed-y vanishing scalar. -/
theorem total_le (k : ℕ) (ρ B Q n lost crt : ℝ) (hn : 1≤n)
    (hR : 1<n^ρ) (hLost : lost≤Q*short n)
    (hCRT : crt≤envelope k (n^ρ) B*short n) :
    envelope k (n^ρ) B*lost+crt+lost≤remainder k ρ B Q n := by
  have hE : 0≤envelope k (n^ρ) B := by
    unfold envelope
    exact pow_nonneg (mul_nonneg (Real.log_nonneg hR.le) (sq_nonneg _)) _
  have H := mul_le_mul_of_nonneg_left hLost hE
  unfold remainder
  nlinarith only [H,hCRT,hLost]

theorem total_tendsto (k : ℕ) (ρ B Q : ℝ) (h : 8*(k:ℝ)*ρ<1) :
    Tendsto (remainder k ρ B Q) atTop (𝓝 0) := by
  have h₀ : Tendsto (fun n : ℝ=>envelope k (n^ρ) B*short n) atTop (𝓝 0) := by
    simpa only [envelope,short,neg_div] using literal_bound_decay k ρ B h
  have h₁ : Tendsto short atTop (𝓝 0) :=
    _root_.tendsto_rpow_neg_atTop (show (0:ℝ)<(1:ℝ)/4 by norm_num)
  have H₀ := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ=>Q+1) atTop (𝓝 (Q+1))).mul h₀
  have H₁ := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ=>Q) atTop (𝓝 Q)).mul h₁
  simpa only [remainder,mul_zero,add_zero] using H₀.add H₁

end ActualTZOrdinaryBoundaryDecay318
