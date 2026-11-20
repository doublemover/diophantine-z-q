module
public import AffineThreePoissonRows318
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public section
noncomputable section
namespace ActualHybridFourierSummability318
open MeasureTheory
open scoped FourierTransform ContDiff
open AffineThreePoissonRows318

/-- The actual pinned quadratic bound, expressed as division by the
frequency envelope. It is valid also at ξ=0. -/
theorem quadratic_row_bound {f : ℝ → ℂ} (h : ContDiff ℝ 2 f)
    (hi : ∀ n≤(2:ℕ),Integrable (iteratedDeriv n f)) (ξ C : ℝ)
    (hC : (∫ v,‖f v‖)+(4*Real.pi^2)⁻¹*(∫ v,‖iteratedDeriv 2 f v‖)≤C) :
    ‖𝓕 f ξ‖≤C/(1+ξ^2) := by
  apply (le_div_iff₀ (by positivity : 0<1+ξ^2)).mpr
  rw [mul_comm]
  exact (Real.one_add_sq_mul_norm_fourier_le h hi ξ).trans hC

@[expose] def delta (H : ℝ) (n : ℤ) : ℝ := (1+freq H n^2)⁻¹

lemma delta_nonneg (H : ℝ) (n : ℤ) : 0≤delta H n := by
  unfold delta
  positivity

/-- A coarse tail comparison suffices for summability at every H>0;
the sharper bound 1+4H follows from a monotone integral estimate. -/
theorem delta_summable (H : ℝ) (hH : 0<H) : Summable (delta H) := by
  have hpow : Summable (fun n : ℤ => |(n:ℝ)|^(-(2:ℝ))) :=
    Real.summable_abs_int_rpow (by norm_num)
  have htail := hpow.mul_left (H^2)
  apply htail.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  have hr : (n:ℝ)≠0 := by exact_mod_cast hn
  have ha : 0<|(n:ℝ)| := abs_pos.mpr hr
  rw [Real.rpow_neg ha.le,Real.rpow_two,abs_sq,norm_of_nonneg (delta_nonneg H n)]
  unfold delta freq
  rw [div_pow,← div_eq_mul_inv]
  calc
    _ ≤ (((n:ℝ)^2)/(H^2))⁻¹ := by
      exact inv_anti₀ (by positivity) (by linarith)
    _ = _ := by field_simp [hH.ne',hr] <;> ring

/-- A single nonnegative product envelope for each mixed stage suffices.
There is no extra independence, conditional rearrangement or discarded phase. -/
theorem swap_sums_of_envelopes {W : Cube} {H c₁ c₂ c₃ : ℝ}
    (a b c e : ℤ → ℝ)
    (ha : Summable a) (hb : Summable b) (hc : Summable c) (he : Summable e)
    (ha₀ : 0≤a) (hb₀ : 0≤b) (hc₀ : 0≤c) (he₀ : 0≤e)
    (h₁ : ∀ i j k, ‖A₁ W H c₁ c₂ c₃ i j k‖≤a i*b j)
    (h₂ : ∀ i j k, ‖A₂ W H c₁ c₂ c₃ i j k‖≤a i*c j*e k) :
    SwapSums W H c₁ c₂ c₃ := by
  have hrow (i k : ℤ) : Summable (fun j => a i*c j*e k) :=
    (hc.mul_left (a i)).mul_right (e k)
  have hnorm (i k : ℤ) : Summable (fun j => ‖A₂ W H c₁ c₂ c₃ i j k‖) :=
    (hrow i k).of_norm_bounded (fun j => by simpa only [norm_of_nonneg (norm_nonneg _)] using h₂ i j k)
  let C : ℝ := ∑' j,c j
  have hC : 0≤C := tsum_nonneg hc₀
  have hmajor (i k : ℤ) :
    ‖∑' j : ℤ,A₂ W H c₁ c₂ c₃ i j k‖≤(a i*C)*e k := by
    calc
      _ ≤ ∑' j : ℤ,‖A₂ W H c₁ c₂ c₃ i j k‖ := norm_tsum_le_tsum_norm (hnorm i k)
      _ ≤ ∑' j : ℤ,a i*c j*e k := (hnorm i k).tsum_le_tsum (fun j => h₂ i j k) (hrow i k)
      _ = _ := by rw [tsum_mul_right,tsum_mul_left]
  refine ⟨?_,?_,?_⟩
  · intro k
    exact (ha.mul_of_nonneg hb ha₀ hb₀).of_norm_bounded (fun p : ℤ×ℤ => h₁ p.1 p.2 k)
  · have hpos : 0≤(fun i => a i*C) := fun i => mul_nonneg (ha₀ i) hC
    exact ((ha.mul_right C).mul_of_nonneg he hpos he₀).of_norm_bounded
      (fun p : ℤ×ℤ => hmajor p.1 p.2)
  · intro i
    have hpos : 0≤(fun j => a i*c j) := fun j => mul_nonneg (ha₀ i) (hc₀ j)
    exact ((hc.mul_left (a i)).mul_of_nonneg he hpos he₀).of_norm_bounded
      (fun p : ℤ×ℤ => h₂ i p.1 p.2)

/-- The sampled primal support is finite for each fixed H>0, including
H<1; no uniform cardinal bound in H is used to exchange the sums. -/
theorem node_band_finite (H c R : ℝ) (hH : 0<H) :
    {n : ℤ | |node H c n|≤R}.Finite := by
  refine (Set.finite_Icc (Int.ceil ((-R-c)/H)) (Int.floor ((R-c)/H))).subset ?_
  intro n hn
  have hh := abs_le.mp (show |node H c n|≤R from hn)
  dsimp [node] at hh
  refine ⟨Int.ceil_le.mpr ((div_le_iff₀ hH).mpr ?_),
    Int.le_floor.mpr ((le_div_iff₀ hH).mpr ?_)⟩
  · simpa only [mul_comm] using (by linarith [hh.1] : -R-c≤H*(n:ℝ))
  · simpa only [mul_comm] using (by linarith [hh.2] : H*(n:ℝ)≤R-c)

@[expose] def band (H c R : ℝ) (n : ℤ) : ℝ := if |node H c n|≤R then 1 else 0

lemma band_nonneg (H c R : ℝ) : 0≤band H c R := by
  intro n
  unfold band
  split_ifs <;> norm_num

lemma band_summable (H c R : ℝ) (hH : 0<H) : Summable (band H c R) := by
  apply summable_of_hasFiniteSupport
  apply (node_band_finite H c R hH).subset
  intro n hn
  change |node H c n|≤R
  by_contra h
  exact hn (by simp [band,h])

lemma coefficient_norm (H c : ℝ) (hH : 0<H) (n : ℤ) : ‖coefficient H c n‖=H⁻¹ := by
  simp [coefficient,phase,norm_mul,Circle.norm_coe,abs_of_pos (inv_pos.mpr hH)]

/-- Compact-chart specialization of the exact finitary/infinite swap
interface. The two hypotheses are actual partial-Fourier estimates,
not the weighted summability conclusions and not a Poisson input. -/
theorem swap_sums_from_chart_decay {W : Cube} {H c₁ c₂ c₃ : ℝ} (hH : 0<H)
    (R₁ R₂ C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (h₁ : ∀ i j k, ‖F₁ W (freq H i) (node H c₂ j) (node H c₃ k)‖≤
      C₁*delta H i*band H c₂ R₁ j)
    (h₂ : ∀ i j k, ‖F₂ W (freq H i) (freq H j) (node H c₃ k)‖≤
      C₂*delta H i*delta H j*band H c₃ R₂ k) :
    SwapSums W H c₁ c₂ c₃ := by
  let C := H⁻¹*C₁+(H⁻¹)^2*C₂
  have hC : 0≤C := by dsimp [C]; positivity
  let a := fun i => C*delta H i
  have ha : Summable a := (delta_summable H hH).mul_left C
  have ha₀ : 0≤a := fun i => mul_nonneg hC (delta_nonneg H i)
  apply swap_sums_of_envelopes a (band H c₂ R₁) (delta H) (band H c₃ R₂)
    ha (band_summable H c₂ R₁ hH) (delta_summable H hH) (band_summable H c₃ R₂ hH)
    ha₀ (band_nonneg H c₂ R₁) (delta_nonneg H) (band_nonneg H c₃ R₂)
  · intro i j k
    rw [A₁,norm_mul,coefficient_norm H c₁ hH]
    have hcoef : H⁻¹*C₁≤C := le_add_of_nonneg_right (by positivity)
    calc
      _ ≤ H⁻¹*(C₁*delta H i*band H c₂ R₁ j) :=
        mul_le_mul_of_nonneg_left (h₁ i j k) (by positivity)
      _ = (H⁻¹*C₁)*delta H i*band H c₂ R₁ j := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (delta_nonneg H i))
        (band_nonneg H c₂ R₁ j)
  · intro i j k
    rw [A₂,norm_mul,norm_mul,coefficient_norm H c₁ hH,coefficient_norm H c₂ hH,←pow_two]
    have hcoef : (H⁻¹)^2*C₂≤C := le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ (H⁻¹)^2*(C₂*delta H i*delta H j*band H c₃ R₂ k) :=
        mul_le_mul_of_nonneg_left (h₂ i j k) (by positivity)
      _ = ((H⁻¹)^2*C₂)*delta H i*delta H j*band H c₃ R₂ k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (delta_nonneg H i))
          (delta_nonneg H j)) (band_nonneg H c₃ R₂ k)

end ActualHybridFourierSummability318
