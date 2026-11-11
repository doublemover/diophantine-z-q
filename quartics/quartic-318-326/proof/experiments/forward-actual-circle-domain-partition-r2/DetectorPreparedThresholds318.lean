module
public import DetectorWeightPreparation318
public section
noncomputable section
namespace DetectorPreparedThresholds318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318 DetectorPrimeProduct318
open DetectorSmallPrimePreparation318 DetectorWeightPreparation318
set_option maxHeartbeats 1000000

/-- The threshold is chosen before u,d and the five selected integer values.
The coefficients remain the actual ones at w, not free bounded replacements. -/
theorem eventual_prepared (p : ℕ) [Fact p.Prime] (w : Assignment) (c : ℚ)
    (hc : c≠0) (A : ℤ) (hA : 0≤A) :
    ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ (k : Fin 5 → ℤ), (∀ j, linear c u d j=(k j:ℚ)) →
      (∀ j, k j≠0) → (∀ j, padicValRat p (k j:ℚ)=0) →
      (∀ j, IsSquare (k j:ℚ_[p])) →
      realChain w c (u/d^2)≠0 ∧ poleInput w c (u/d^2)≠0 ∧
      IsSquare (poleInput w c (u/d^2):ℚ_[p]) ∧
      A≤padicValRat p (poleInput w c (u/d^2)) := by
  obtain ⟨N,hN⟩ := eventual_leaf_depths p w c hc
  refine ⟨max N (6*|padicValRat p c|+|padicValRat p (2:ℚ)|+A+1),?_⟩
  intro u d hd hdepth k hk hkn hku hks
  have hlow : N≤padicValRat p d := le_trans (le_max_left _ _) hdepth
  have hhigh : 6*|padicValRat p c|+|padicValRat p (2:ℚ)|+A+1≤padicValRat p d :=
    le_trans (le_max_right _ _) hdepth
  have hc₁ := le_abs_self (padicValRat p c)
  have hc₂ := neg_le_abs (padicValRat p c)
  have h2₁ := le_abs_self (padicValRat p (2:ℚ))
  have h2₂ := neg_le_abs (padicValRat p (2:ℚ))
  have hdeep : padicValRat p c<padicValRat p d := by omega
  obtain ⟨hr,hb,hv⟩ := pole_value p w c u d hc hd k hk hkn hku hdeep
    (hN u d hd hlow k hk hkn hku)
  refine ⟨hr,hb,pole_local_square w c u d hc hd k hk hks,?_⟩
  rw [hv]
  omega

/-- Every finite family of actual coefficient arrays has one common threshold.
This finite uniformity does not assert bounds on an infinite local orbit. -/
theorem finite_uniform (p : ℕ) [Fact p.Prime] (w : Fin 3 → Assignment)
    (c : Fin 3 → ℚ) (hc : ∀ j, c j≠0) (A : ℤ) (hA : 0≤A) :
    ∃ N : ℤ, ∀ j : Fin 3, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ (k : Fin 5 → ℤ), (∀ i, linear (c j) u d i=(k i:ℚ)) →
      (∀ i, k i≠0) → (∀ i, padicValRat p (k i:ℚ)=0) →
      (∀ i, IsSquare (k i:ℚ_[p])) →
      realChain (w j) (c j) (u/d^2)≠0 ∧ poleInput (w j) (c j) (u/d^2)≠0 ∧
      IsSquare (poleInput (w j) (c j) (u/d^2):ℚ_[p]) ∧
      A≤padicValRat p (poleInput (w j) (c j) (u/d^2)) := by
  have he : ∀ j : Fin 3, ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ (k : Fin 5 → ℤ), (∀ i, linear (c j) u d i=(k i:ℚ)) →
      (∀ i, k i≠0) → (∀ i, padicValRat p (k i:ℚ)=0) →
      (∀ i, IsSquare (k i:ℚ_[p])) →
      realChain (w j) (c j) (u/d^2)≠0 ∧ poleInput (w j) (c j) (u/d^2)≠0 ∧
      IsSquare (poleInput (w j) (c j) (u/d^2):ℚ_[p]) ∧
      A≤padicValRat p (poleInput (w j) (c j) (u/d^2)) :=
    fun j => eventual_prepared p (w j) (c j) (hc j) A hA
  choose N hN using he
  refine ⟨∑ j : Fin 3, |N j|,?_⟩
  intro j u d hd hdepth
  apply hN j u d hd
  exact le_trans (le_trans (le_abs_self (N j))
    (Finset.single_le_sum (fun i _ => abs_nonneg (N i)) (Finset.mem_univ j))) hdepth

end DetectorPreparedThresholds318
