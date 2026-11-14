module
public import ActualPrimeTailGeometric318
public section
noncomputable section
namespace ActualMovingBoundaryPrimeTail318
open scoped BigOperators
open ActualPrimeDyadicPower318 ActualPrimeTailGeometric318
set_option maxHeartbeats 20000000

@[expose] def delta (N : ℕ) : ℝ := 1/Real.log (N:ℝ)
@[expose] def sigma (N : ℕ) : ℝ := 1+delta N
lemma delta_pos (N : ℕ) (hN : 1<N) : 0<delta N :=
  one_div_pos.mpr (Real.log_pos (by exact_mod_cast hN))
lemma sigma_gt_one (N : ℕ) (hN : 1<N) : 1<sigma N := by
  have hh := delta_pos N hN
  dsimp [sigma]
  linarith

/-- Elementary quantitative replacement for merely saying that
1-exp(-x) is asymptotic to x. -/
lemma exponential_gap (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) :
    x/2≤1-Real.exp (-x) := by
  have he : 1+x≤Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
  have hd : 0<1+x := by linarith
  have hi := one_div_le_one_div_of_le hd he
  have hrat : 1/(1+x)≤1-x/2 := by
    apply (div_le_iff₀ hd).mpr
    have hprod := mul_nonneg hx0 (show 0≤1-x by linarith)
    nlinarith
  have hh : Real.exp (-x)≤1-x/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using hi.trans hrat
  linarith

lemma moving_geometric_gap (N : ℕ) (hN : 1<N) :
    Real.log 2/2≤Real.log (N:ℝ)*(1-ratio (delta N)) := by
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  have hlog2 : Real.log (2:ℝ)≤Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN2
  let x := Real.log 2/Real.log (N:ℝ)
  have hx0 : 0≤x := (div_pos h2 hlog).le
  have hx1 : x≤1 := (div_le_iff₀ hlog).mpr (by simpa only [one_mul] using hlog2)
  have he : ratio (delta N)=Real.exp (-x) := by
    rw [ratio,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    dsimp [x,delta]
    ring
  have hh := mul_le_mul_of_nonneg_left (exponential_gap x hx0 hx1) hlog.le
  rw [←he] at hh
  have hid : Real.log (N:ℝ)*(x/2)=Real.log 2/2 := by
    dsimp [x]
    field_simp [hlog.ne']
  rw [hid] at hh
  exact hh

/-- A fixed numerical bound for the actual finite prime tail at the
MOVING exponent sigma(N)=1+1/logN. This is the missing uniformity
needed before comparing finite Euler products to L-functions at1. -/
theorem actual_moving_prime_tail (N : ℕ) (hN : 1<N) (S : Finset ℕ)
    (hS : ∀p∈S,p.Prime ∧ N≤p) :
    (∑p∈S,(p:ℝ)^(-sigma N))≤4*Real.log 4/Real.log 2 := by
  have hδ := delta_pos N hN
  have ht := actual_finite_prime_tail N hN (delta N) hδ S hS
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h4 : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hr : 0<1-ratio (delta N) := by linarith [(ratio_bounds _ hδ).2]
  have hp : (N:ℝ)^(-delta N)≤1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega)) (show -delta N≤0 by linarith)
    simpa only [Real.rpow_zero] using hh
  have hA : amplitude N (delta N)/(1-ratio (delta N))≤
      2*Real.log 4/(Real.log (N:ℝ)*(1-ratio (delta N))) := by
    unfold amplitude
    have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) h4)
    have hd := div_le_div_of_nonneg_right hh (mul_pos hlog hr).le
    convert hd using 1 <;> field_simp [hlog.ne',hr.ne'] <;> ring
  have hgap := moving_geometric_gap N hN
  have hrec := one_div_le_one_div_of_le (div_pos h2 (by norm_num)) hgap
  have hlast : 2*Real.log 4/(Real.log (N:ℝ)*(1-ratio (delta N)))≤
      4*Real.log 4/Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hrec (mul_nonneg (by norm_num) h4)
    convert hh using 1 <;> field_simp [hlog.ne',hr.ne',h2.ne'] <;> ring
  exact ht.trans (hA.trans hlast)

end ActualMovingBoundaryPrimeTail318
