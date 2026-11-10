module
public import SeventeenOrbitPrecision318
public section
noncomputable section
namespace AllSmallPrimeProgression318
open ActualOrbitLocalFilter318 ActualOrbitTranslatedAccess318 SourceLocalProgression318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The actual17-adic chart enters every identity neighborhood on a
constructed progression. Every signed multiplier is allowed. -/
lemma identity_access (U : Set (Fin 4 → ℚ_[17])) (hU : U∈𝓝 0) :
    ∃ E : ℕ, ∀ m : ℤ, error 17 (20*17^E*m)∈U := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨E,hE⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (17:ℝ)⁻¹<1)
  refine ⟨E,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_zero_right]
  exact lt_of_le_of_lt (SeventeenOrbitPrecision318.error_bound E m) hE

lemma translated_access (n : ℤ) (U : Set (Fin 4 → ℚ_[17]))
    (hU : U∈𝓝 (error 17 n)) :
    ∃ E : ℕ, ∀ m : ℤ, error 17 (n+20*17^E*m)∈U := by
  have ht : (translate 17 n) ⁻¹' U∈𝓝 (0 : Fin 4 → ℚ_[17]) :=
    (translate_continuousAt 17 n) (by simpa only [translate_zero] using hU)
  obtain ⟨E,hE⟩ := identity_access _ ht
  refine ⟨E,fun m => ?_⟩
  simpa only [Set.mem_preimage,translate_error] using hE m

/-- Actual affine index regularity at17, now in the same positive-modulus
interface as2 and3. No17-adic access hypothesis is left to the caller. -/
lemma actual_chart (a b h₀ : ℤ) :
    LocalIndexRegularity318.Regular h₀ (fun h => error 17 (a+b*h)) := by
  intro U hU
  obtain ⟨E,hE⟩ := translated_access (a+b*h₀) U hU
  refine ⟨20*17^E,by positivity,fun m => ?_⟩
  have hm := hE (b*m)
  have hi : a+b*(h₀+((20*17^E:ℕ):ℤ)*m)=a+b*h₀+20*(17:ℤ)^E*(b*m) := by
    push_cast
    ring
  rw [hi]
  exact hm

/-- A single positive modulus preserves every earlier modulus M and gives
actual source preparation at2,3,17. Labels and center precede all three
thresholds and the modulus; u,d and the final h follow them. The same literal
pole coordinates190,241,292 and actual contact factors are used throughout. -/
theorem simultaneous (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ M : ℕ) (hM : 0<M) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ))) :
    ∃ (L : ℕ) (N₂ N₃ N₁₇ : ℤ), 0<L ∧ M∣L ∧
      Prepared 2 q labels h₀ L N₂ 3 ∧ Prepared 3 q labels h₀ L N₃ 1 ∧
      Prepared 17 q labels h₀ L N₁₇ 2 := by
  obtain ⟨L₂₃,N₂,N₃,hL₂₃,hM₂₃,h₂,h₃⟩ := two_three q labels hn h₀ M hM hzero hone hg
  obtain ⟨L₁₇,N₁₇,hL₁₇,h₁₇⟩ := prepared_progression 17 actual_chart
    q labels hn h₀ hzero hone hg 2 (by norm_num)
  let L := L₂₃*L₁₇
  have hd₂₃ : L₂₃∣L := dvd_mul_right _ _
  have hd₁₇ : L₁₇∣L := dvd_mul_left _ _
  refine ⟨L,N₂,N₃,N₁₇,Nat.mul_pos hL₂₃ hL₁₇,hM₂₃.trans hd₂₃,?_,?_,?_⟩
  · exact Prepared.of_dvd 2 q labels h₀ L₂₃ L N₂ 3 h₂ hd₂₃
  · exact Prepared.of_dvd 3 q labels h₀ L₂₃ L N₃ 1 h₃ hd₂₃
  · exact Prepared.of_dvd 17 q labels h₀ L₁₇ L N₁₇ 2 h₁₇ hd₁₇

end AllSmallPrimeProgression318
