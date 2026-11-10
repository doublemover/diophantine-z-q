module
public import ActualOrbitCoefficientDepth318
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public section
noncomputable section
namespace ActualOrbitLocalFilter318
open CoherentMultipleCharts318 ActualOrbitCoefficientDepth318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The four rational coordinates of the actual oriented chart, measured
from its positive identity. In particular the third entry is v.re−1. -/
@[expose] def error (p : ℕ) [Fact p.Prime] (n : ℤ) : Fin 4 → ℚ_[p] :=
  ![((chartU n).re:ℚ_[p]),((chartU n).im:ℚ_[p]),
    ((chartV n-1).re:ℚ_[p]),((chartV n-1).im:ℚ_[p])]

@[simp] lemma error_zero (p : ℕ) [Fact p.Prime] : error p 0=0 := by
  ext i
  fin_cases i <;> simp [error]

lemma six_two : padicValNat 2 6=1 := by
  rw [show (6:ℕ)=2*3 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self,padicValNat_primes (by decide : 2≠3)]
  norm_num

lemma six_three : padicValNat 3 6=1 := by
  rw [show (6:ℕ)=3*2 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self,padicValNat_primes (by decide : 3≠2)]
  norm_num

lemma six_depth (p : ℕ) [Fact p.Prime] (h6 : padicValNat p 6=1)
    (e : ℕ) (m : ℤ) (hm : m≠0) :
    padicValInt p ((6:ℤ)^e*m)=e+padicValInt p m := by
  change padicValNat p (((6:ℤ)^e*m).natAbs)=e+padicValNat p m.natAbs
  rw [Int.natAbs_mul,Int.natAbs_pow]
  change padicValNat p ((6:ℕ)^e*m.natAbs)=e+padicValNat p m.natAbs
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (Int.natAbs_ne_zero.mpr hm),
    padicValNat.pow,h6,mul_one]

lemma norm_of_depth (p : ℕ) [Fact p.Prime] (e : ℕ) (q : ℚ)
    (hq : (e:WithTop ℤ)≤ConcretePadic318.rationalPlace p q) :
    ‖(q:ℚ_[p])‖≤((p:ℝ)⁻¹)^e := by
  rw [PadicDetectorCoefficients318.rational_embedding] at hq
  have hn := (HTail318.norm_le_iff_valuation p (q:ℚ_[p]) (e:ℤ)).mpr hq
  simpa only [zpow_neg,zpow_natCast,inv_pow] using hn

/-- Uniform in every integer multiplier, including zero and negative ones.
The common modulus is literal 4·6^e, not an existence premise about an orbit. -/
theorem two_error_bound (e : ℕ) (m : ℤ) :
    ‖error 2 (4*6^e*m)‖≤((2:ℝ)⁻¹)^e := by
  by_cases hm : m=0
  · subst m
    simp
  have hd := six_depth 2 six_two e m hm
  have hu := two_chart ((6:ℤ)^e*m) (chartU (4*(6^e*m))) (by simp)
  have hv := two_chart ((6:ℤ)^e*m) (chartV (4*(6^e*m))-1) (by simp)
  rw [hd] at hu hv
  have hl : (e:WithTop ℤ)≤((1+((e+padicValInt 2 m:ℕ):ℤ):ℤ):WithTop ℤ) := by
    exact_mod_cast (show (e:ℤ)≤1+((e+padicValInt 2 m:ℕ):ℤ) by omega)
  rw [mul_assoc]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact norm_of_depth 2 e _ (le_trans hl hu.1)
  · exact norm_of_depth 2 e _ (le_trans hl hu.2)
  · exact norm_of_depth 2 e _ (le_trans hl hv.1)
  · exact norm_of_depth 2 e _ (le_trans hl hv.2)

theorem three_error_bound (e : ℕ) (m : ℤ) :
    ‖error 3 (4*6^e*m)‖≤((3:ℝ)⁻¹)^e := by
  by_cases hm : m=0
  · subst m
    simp
  have hd := six_depth 3 six_three e m hm
  have hu := three_chart ((6:ℤ)^e*m) (chartU (4*(6^e*m))) (by simp)
  have hv := three_chart ((6:ℤ)^e*m) (chartV (4*(6^e*m))-1) (by simp)
  rw [hd] at hu hv
  have hl : (e:WithTop ℤ)≤((1+((e+padicValInt 3 m:ℕ):ℤ):ℤ):WithTop ℤ) := by
    exact_mod_cast (show (e:ℤ)≤1+((e+padicValInt 3 m:ℕ):ℤ) by omega)
  rw [mul_assoc]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact norm_of_depth 3 e _ (le_trans hl hu.1)
  · exact norm_of_depth 3 e _ (le_trans hl hu.2)
  · exact norm_of_depth 3 e _ (le_trans hl hv.1)
  · exact norm_of_depth 3 e _ (le_trans hl hv.2)

/-- From the quantitative actual-chart bound to every open identity
neighborhood. The exponent is chosen before the arbitrary later multiplier. -/
lemma access_of_bound (p : ℕ) [Fact p.Prime]
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    (U : Set (Fin 4 → ℚ_[p])) (hU : IsOpen U) (h0 : 0∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error p (4*6^e*m)∈U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ)<p := lt_trans zero_lt_one hp
  have hpos : (0:ℝ)<(p:ℝ)⁻¹ := inv_pos.mpr hp0
  have hmul : (p:ℝ)*(p:ℝ)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hp0)
  have hinv : (p:ℝ)⁻¹<1 := by nlinarith
  obtain ⟨e,he⟩ := exists_pow_lt_of_lt_one hε hinv
  refine ⟨e,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_zero_right]
  exact lt_of_le_of_lt (hb e m) he

theorem two_access (U : Set (Fin 4 → ℚ_[2])) (hU : IsOpen U) (h0 : 0∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error 2 (4*6^e*m)∈U :=
  access_of_bound 2 two_error_bound U hU h0

theorem three_access (U : Set (Fin 4 → ℚ_[3])) (hU : IsOpen U) (h0 : 0∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error 3 (4*6^e*m)∈U :=
  access_of_bound 3 three_error_bound U hU h0

end ActualOrbitLocalFilter318
