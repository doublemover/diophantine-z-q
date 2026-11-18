module
public import ActualOriginalDyadicFullRecurrence318
public section
noncomputable section
namespace ActualOriginalDyadicDensity318
open Filter ActualFullLocalDensityRecurrence318 ActualOriginalDyadicFullRecurrence318
open ActualOriginalDyadicPrimitiveCount318 ActualOriginalLocalDensityLimit318
open scoped Topology
set_option maxHeartbeats 28000000

/-- Actual positive-exponent dyadic counts on both parity subsequences.
The two initial values are the genuine original mod2 and mod4 counts. -/
theorem actual_original_dyadic_even_odd (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hn4 : ¬(2:ℤ)^2∣κ) (h8 : (κ:ZMod 8)=6)
    (h2 : (κ:ZMod 2)=0) (h4 : (κ:ZMod 4)=2) (e : ℕ) :
    volume κ 2 (2*e+1)=8/7+(1-8/7)*(1/8:ℚ)^e ∧
    volume κ 2 (2*e+2)=8/7+(1-8/7)*(1/8:ℚ)^e := by
  induction e with
  | zero =>
    have hh := actual_original_dyadic_initial_volumes κ h2 h4
    norm_num only [mul_zero,zero_add,pow_zero,mul_one] at ⊢
    constructor <;> linarith [hh.1,hh.2]
  | succ e ih =>
    have he1 : 2*(e+1)+1=2*e+3 := by omega
    have he2 : 2*(e+1)+2=(2*e+1)+3 := by omega
    rw [he1,he2,actual_original_dyadic_volume_recurrence κ hκ hn4 h8 (2*e),
      actual_original_dyadic_volume_recurrence κ hκ hn4 h8 (2*e+1)]
    change 1+volume κ 2 (2*e+1)/8=_ ∧ 1+volume κ 2 (2*e+2)/8=_
    rw [ih.1,ih.2,pow_succ (1/8:ℚ) e]
    constructor <;> ring

theorem actual_original_dyadic_formula (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hn4 : ¬(2:ℤ)^2∣κ) (h8 : (κ:ZMod 8)=6)
    (h2 : (κ:ZMod 2)=0) (h4 : (κ:ZMod 4)=2) (n : ℕ) :
    volume κ 2 (n+1)=8/7+(1-8/7)*(1/8:ℚ)^(n/2) := by
  have hh := actual_original_dyadic_even_odd κ hκ hn4 h8 h2 h4 (n/2)
  have hc : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hc with he|ho
  · exact (congrArg (fun t => volume κ 2 (t+1)) he).trans hh.1
  · exact (congrArg (fun t => volume κ 2 (t+1)) ho).trans hh.2

/-- Genuine unrestricted dyadic density of the SAME original diagonal
quadric. The value8/7 follows from constructed original residue counts,
not from the odd-prime formula or a determinant-changing substitution. -/
theorem actual_original_dyadic_limit (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hn4 : ¬(2:ℤ)^2∣κ) (h8 : (κ:ZMod 8)=6)
    (h2 : (κ:ZMod 2)=0) (h4 : (κ:ZMod 4)=2) :
    Tendsto (fun n : ℕ => (volume κ 2 n:ℝ)) atTop (𝓝 (8/7:ℝ)) := by
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/8) (by norm_num : (1/8:ℝ)<1)).comp original_half_exponent_tendsto
  have hs : Tendsto (fun n : ℕ => (volume κ 2 (n+1):ℝ)) atTop (𝓝 (8/7:ℝ)) := by
    have he (n : ℕ) : (volume κ 2 (n+1):ℝ)=8/7+(1-8/7)*(1/8:ℝ)^(n/2) := by
      rw [actual_original_dyadic_formula κ hκ hn4 h8 h2 h4 n]
      simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,
        Rat.cast_div,Rat.cast_ofNat]
    simp_rw [he]
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul hg)
  have hp : Tendsto (fun n : ℕ => n-1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b+1,fun n hn => by omega⟩
  have hh := hs.comp hp
  refine Tendsto.congr' ?_ hh
  exact eventually_atTop.2 ⟨1,fun n hn => by
    change (volume κ 2 (n-1+1):ℝ)=(volume κ 2 n:ℝ)
    rw [Nat.sub_add_cancel hn]⟩

theorem original_318_at_two :
    Tendsto (fun n : ℕ => (volume 318 2 n:ℝ)) atTop (𝓝 (8/7:ℝ)) :=
  actual_original_dyadic_limit 318 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem original_326_at_two :
    Tendsto (fun n : ℕ => (volume 326 2 n:ℝ)) atTop (𝓝 (8/7:ℝ)) :=
  actual_original_dyadic_limit 326 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The actual dyadic primitive volume has precisely the SAME
singular correction exponent3 as the full primitive normalization. -/
theorem actual_dyadic_primitive_normalization (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hn4 : ¬(2:ℤ)^2∣κ) (h8 : (κ:ZMod 8)=6) (e : ℕ) :
    (Nat.card (ActualPrimitivePrimePower318.PrimitiveResidues κ (2^(e+3)) 2):ℚ)/
      (2:ℚ)^(4*(e+3))=(8/7:ℚ)*(1-1/(2:ℚ)^3) := by
  rw [actual_dyadic_primitive_volume κ hκ hn4 h8 e]
  norm_num

end ActualOriginalDyadicDensity318
