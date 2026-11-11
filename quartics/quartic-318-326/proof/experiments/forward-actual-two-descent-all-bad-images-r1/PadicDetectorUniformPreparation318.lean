module
public import PadicDetectorCoefficients318
public section
noncomputable section
namespace PadicDetectorUniformPreparation318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318 DetectorPrimeProduct318
open DetectorSmallPrimePreparation318 DetectorWeightPreparation318
open PadicDetectorCoefficients318 Set
set_option maxHeartbeats 1000000

/-- A coefficient bound fixed on a genuine p-adic neighborhood yields a
single threshold before both the parameter and the later assignment. -/
theorem uniform_on_bound (p : ℕ) [Fact p.Prime] (U : Set (Coeff ℚ_[p])) (B : ℤ)
    (hB : ∀ w : Assignment, project p w∈U → ∀ a∈coefficients w,
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.re ∧
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.im)
    (c : ℚ) (hc : c≠0) (A : ℤ) (hA : 0≤A) :
    ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ w : Assignment, project p w∈U →
      ∀ (k : Fin 5 → ℤ), (∀ j, linear c u d j=(k j:ℚ)) →
      (∀ j, k j≠0) → (∀ j, padicValRat p (k j:ℚ)=0) →
      (∀ j, IsSquare (k j:ℚ_[p])) →
      realChain w c (u/d^2)≠0 ∧ poleInput w c (u/d^2)≠0 ∧
      IsSquare (poleInput w c (u/d^2):ℚ_[p]) ∧
      A≤padicValRat p (poleInput w c (u/d^2)) := by
  refine ⟨|B|+244*|padicValRat p c|+|padicValRat p (2:ℚ)|+A+1,?_⟩
  intro u d hd hN w hw k hk hkn hku hks
  have hB₁ := le_abs_self B
  have hB₂ := neg_le_abs B
  have hc₁ := le_abs_self (padicValRat p c)
  have hc₂ := neg_le_abs (padicValRat p c)
  have h2₁ := le_abs_self (padicValRat p (2:ℚ))
  have h2₂ := neg_le_abs (padicValRat p (2:ℚ))
  have hdeep : padicValRat p c<padicValRat p d := by omega
  obtain ⟨hq,h0,h1,h2⟩ := weight_values p c u d hc hd k hk hkn hku hdeep
  have hv : ∀ j, -B<padicValRat p (weights c (u/d^2) j) := by
    intro j
    fin_cases j
    · rw [h0]; omega
    · rw [h1]; omega
    · rw [h2]; omega
  have hleaf := weighted_depths p w c (u/d^2) B (hB w hw) hq hv
  obtain ⟨hr,hb,hval⟩ := pole_value p w c u d hc hd k hk hkn hku hdeep hleaf
  refine ⟨hr,hb,pole_local_square w c u d hc hd k hk hks,?_⟩
  rw [hval]
  omega

/-- Actual neighborhood and one threshold for all three fixed scales. The
later rational assignment may vary arbitrarily inside this same neighborhood. -/
theorem three_scales (p : ℕ) [Fact p.Prime] (w₀ : Assignment)
    (c : Fin 3 → ℚ) (hc : ∀ j, c j≠0) (A : ℤ) (hA : 0≤A) :
    ∃ U : Set (Coeff ℚ_[p]), IsOpen U ∧ project p w₀∈U ∧
      ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ w : Assignment, project p w∈U → ∀ j : Fin 3,
      ∀ (k : Fin 5 → ℤ), (∀ i, linear (c j) u d i=(k i:ℚ)) →
      (∀ i, k i≠0) → (∀ i, padicValRat p (k i:ℚ)=0) →
      (∀ i, IsSquare (k i:ℚ_[p])) →
      realChain w (c j) (u/d^2)≠0 ∧ poleInput w (c j) (u/d^2)≠0 ∧
      IsSquare (poleInput w (c j) (u/d^2):ℚ_[p]) ∧
      A≤padicValRat p (poleInput w (c j) (u/d^2)) := by
  obtain ⟨U,hU,hcenter,B,_,hB⟩ := actual_neighborhood p w₀
  have he := fun j => uniform_on_bound p U B hB (c j) (hc j) A hA
  choose N hN using he
  refine ⟨U,hU,hcenter,∑ j : Fin 3, |N j|,?_⟩
  intro u d hd hdepth w hw j
  apply hN j u d hd _ w hw
  exact le_trans (le_trans (le_abs_self (N j))
    (Finset.single_le_sum (fun i _ => abs_nonneg (N i)) (Finset.mem_univ j))) hdepth

end PadicDetectorUniformPreparation318
