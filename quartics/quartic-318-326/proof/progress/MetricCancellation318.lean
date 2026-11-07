module
public import Contact49Growth318
public import FiveContactMetricBounds318
public import Mathlib.Analysis.Real.Pi.Bounds
public section
noncomputable section
namespace MetricCancellation318
set_option maxHeartbeats 0

@[expose] def average {ι : Type*} (s : Finset ι) (degree : ℝ) (f : ι→ℝ) : ℝ :=
  (∑i∈s,f i)/degree

theorem average_add {ι : Type*} (s : Finset ι) (degree : ℝ) (a b : ι→ℝ) :
    average s degree (fun i=>a i+b i)=average s degree a+average s degree b := by
  simp only [average,Finset.sum_add_distrib,add_div]

theorem average_mul {ι : Type*} (s : Finset ι) (degree k : ℝ) (a : ι→ℝ) :
    average s degree (fun i=>k*a i)=k*average s degree a := by
  simp only [average,←Finset.mul_sum]
  ring

/-- The two Arakelov coordinate metrics cancel at every embedding with their exact common weight. -/
theorem exact_metric_cancellation {ι : Type*} (s : Finset ι) (degree k F hb hFal : ℝ)
    (a m w : ι→ℝ) (hk : 0≤k)
    (hbnd : hb≤F-average s degree (fun i=>a i+m i))
    (hFalbnd : hFal≤k*hb+average s degree (fun i=>w i+k*m i)) :
    hFal≤k*F-k*average s degree a+average s degree w := by
  rw [average_add] at hbnd
  rw [average_add,average_mul] at hFalbnd
  have h := mul_le_mul_of_nonneg_left hbnd hk
  nlinarith

/-- The GR/Rémond correction is less than g, in the stated normalization. -/
theorem normalization_log_bound : Real.log (Real.sqrt Real.pi)<1 := by
  rw [Real.log_sqrt Real.pi_pos.le]
  have hp := Real.log_lt_log Real.pi_pos Real.pi_lt_four
  rw [Real.log_four_eq] at hp
  linarith [Real.log_two_lt_d9]

theorem normalization_shift (g hFal : ℝ) (hg : 0≤g) :
    hFal+g*Real.log (Real.sqrt Real.pi)≤hFal+g := by
  have h := mul_le_mul_of_nonneg_left normalization_log_bound.le hg
  linarith

theorem wronskian_weight_bound (g d : ℝ) (hg : 1≤g) (hgd : g≤d) :
    0≤g*(g+1)/2 ∧ g*(g+1)/2≤d^2 := by
  have hd : 0≤d := by linarith
  constructor
  · positivity
  · nlinarith [sq_nonneg (d-g)]

theorem finite_log_budget (A B L : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hAL : A≤L) (hBL : B≤L) : 2*A*B/Real.log 2≤4*L^2 := by
  have hL : 0≤L := hA.trans hAL
  have hab : A*B≤L^2 := by nlinarith [mul_le_mul hAL hBL hB hL]
  have hl : (1:ℝ)/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg L)
  nlinarith

/-- Explicit scalar aggregation of the finite-divisor, differential, Wronskian and normalization inputs. -/
theorem jacobian_GR_budget (g d L A B ha F delta W hFal hGR : ℝ)
    (hg : 1≤g) (hgd : g≤d) (hL : 1≤L)
    (hA : 0≤A) (hB : 0≤B) (hAL : A≤L) (hBL : B≤L)
    (hha : ha≤100+3*L)
    (hF : F≤3*ha+2*A*B/Real.log 2)
    (hdelta : delta≤ha+9)
    (hW : W≤100*d^2*L)
    (hFalb : hFal≤g*(g+1)/2*F+g*(g+1)/2*delta+W)
    (hGRb : hGR≤hFal+g) :
    hGR≤2^11*d^2*L^2 := by
  have hd : 1≤d := hg.trans hgd
  obtain ⟨hk0,hkd⟩ := wronskian_weight_bound g d hg hgd
  have hf := finite_log_budget A B L hA hB hAL hBL
  have hL2 : L≤L^2 := by nlinarith
  have hL21 : 1≤L^2 := by nlinarith
  have hfd : F+delta≤425*L^2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hfd hk0
  have hmul' := mul_le_mul_of_nonneg_right hkd (show 0≤425*L^2 by positivity)
  have hw := mul_le_mul_of_nonneg_left hL2 (show 0≤100*d^2 by positivity)
  have hg' : g≤d^2 := by nlinarith
  have hg'' : d^2≤d^2*L^2 := by nlinarith [mul_le_mul_of_nonneg_left hL21 (sq_nonneg d)]
  have h526 : hGR≤526*d^2*L^2 := by nlinarith
  exact h526.trans (by nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg L)])


/-- Full real-log budget for the retained geometric comparison(G), including the exact pi normalization. -/
theorem geometric_additive_lt_120 :
    2*Real.log Real.pi+Real.log 210+2*Real.log 2765952000+
      Real.log (4*12540153541944538512)+Real.log 32<120 := by
  have hn : (210:ℝ)*2765952000^2*(4*12540153541944538512)*32*16<2^160 := by
    exact_mod_cast FiveContactMetricBounds318.additive_budget_integer
  have hl := Real.log_lt_log
    (by positivity : (0:ℝ)<210*2765952000^2*(4*12540153541944538512)*32*16) hn
  rw [Real.log_pow] at hl
  rw [Real.log_mul (by norm_num : (210:ℝ)*2765952000^2*(4*12540153541944538512)*32≠0) (by norm_num : (16:ℝ)≠0),
    Real.log_mul (by norm_num : (210:ℝ)*2765952000^2*(4*12540153541944538512)≠0) (by norm_num : (32:ℝ)≠0),
    Real.log_mul (by norm_num : (210:ℝ)*2765952000^2≠0) (by norm_num : (4*12540153541944538512:ℝ)≠0),
    Real.log_mul (by norm_num : (210:ℝ)≠0) (by norm_num : (2765952000:ℝ)^2≠0),
    Real.log_pow] at hl
  have hp := Real.log_lt_log Real.pi_pos Real.pi_lt_four
  have h16 : Real.log (16:ℝ)=2*Real.log 4 := by
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow]
    norm_num
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := Real.log_four_eq
  rw [h16] at hl
  norm_num only [Nat.cast_ofNat] at hl
  norm_num only [show (4*12540153541944538512:ℝ)=50160614167778154048 by norm_num]
  linarith [Real.log_two_lt_d9]

end MetricCancellation318
#print axioms MetricCancellation318.exact_metric_cancellation
#print axioms MetricCancellation318.normalization_log_bound
#print axioms MetricCancellation318.jacobian_GR_budget

#print axioms MetricCancellation318.geometric_additive_lt_120
