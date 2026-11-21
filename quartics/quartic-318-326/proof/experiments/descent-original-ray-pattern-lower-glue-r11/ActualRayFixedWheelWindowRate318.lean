module
public import Mathlib
public section
noncomputable section
namespace ActualRayFixedWheelWindowRate318
open Filter
open scoped Topology Real

/-- The old height is a floor before the step quotient. Keeping W
fixed, both this floor and the genuine prime cutoff are absorbed by
a SINGLE eventual N threshold, not by a new subsequence. -/
theorem eventual (W : ℕ) (hW : 0 < W) (τ ρ S Z : ℝ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hS : 0 < S) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let n := N/W
      let T := ⌊τ*Real.sqrt (N:ℝ)⌋₊
      2000*W ≤ N ∧ 200*W ≤ T ∧ T ≤ N ∧
      6400*Z*(W:ℝ) ≤ S*(T:ℝ) ∧
      0 < n ∧ 2*(W:ℤ) < (N:ℤ) ∧
      (N:ℤ) ≤ (W:ℤ)*((n:ℤ)+1) ∧
      2*((W:ℤ)*(⌈(n:ℝ)^ρ⌉₊:ℤ)) < (N:ℤ) := by
  have hp : 0 < 1-ρ := sub_pos.mpr hρ1
  obtain ⟨X,hX⟩ := (eventually_atTop.1 ((tendsto_atTop.1
    (_root_.tendsto_rpow_atTop hp)) (8:ℝ)))
  obtain ⟨U,hU⟩ := exists_nat_gt (max (8:ℝ) X)
  obtain ⟨V,hV⟩ := exists_nat_gt
    (max (200*(W:ℝ)) (6400*Z*(W:ℝ)/S))
  let P := ⌈(V:ℝ)/τ⌉₊
  refine ⟨max (2000*W) (max (U*W) (P^2)),?_⟩
  intro N hN
  let n := N/W
  let T := ⌊τ*Real.sqrt (N:ℝ)⌋₊
  have hnW : 2000*W ≤ N := (le_max_left _ _).trans hN
  have hnU : U*W ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hnP : P^2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hUn : U ≤ n := (Nat.le_div_iff_mul_le hW).2 hnU
  have hUn' : (U:ℝ) ≤ n := by exact_mod_cast hUn
  have hn8 : (8:ℝ) ≤ n := (le_max_left _ _).trans (hU.le.trans hUn')
  have hnX : X ≤ (n:ℝ) := (le_max_right _ _).trans (hU.le.trans hUn')
  have hnpos : (0:ℝ) < n := by linarith only [hn8]
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have hPref := mul_le_mul_of_nonneg_left (hX (n:ℝ) hnX)
    (Real.rpow_nonneg hnpos.le ρ)
  rw [←Real.rpow_add hnpos,show ρ+(1-ρ)=1 by ring,Real.rpow_one] at hPref
  have hCeil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le ρ)
  have hSmall : (2:ℝ)*(⌈(n:ℝ)^ρ⌉₊:ℝ) < (n:ℝ) := by
    linarith only [hPref,hCeil,hn8]
  have hWr : (0:ℝ) < W := by exact_mod_cast hW
  have hs := mul_lt_mul_of_pos_left hSmall hWr
  have hWN : W*n ≤ N := by
    change W*(N/W) ≤ N
    rw [mul_comm]
    exact Nat.div_mul_le_self N W
  have hWNr : (W:ℝ)*(n:ℝ) ≤ N := by exact_mod_cast hWN
  have hPowW : (2:ℝ)*((W:ℝ)*(⌈(n:ℝ)^ρ⌉₊:ℝ)) < (W:ℝ)*(n:ℝ) := by
    nlinarith only [hs]
  have hPow := hPowW.trans_le hWNr
  have hR : N ≤ W*(n+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    have hm : W*n+N%W = N := Nat.div_add_mod N W
    have hr := Nat.mod_lt N hW
    omega
  have hPN : (P:ℝ)^2 ≤ (N:ℝ) := by exact_mod_cast hnP
  have hP : (V:ℝ)/τ ≤ (P:ℝ) := Nat.le_ceil _
  have hSQ := Real.sqrt_le_sqrt hPN
  rw [Real.sqrt_sq (show 0 ≤ (P:ℝ) by positivity)] at hSQ
  have hVT : V ≤ T := (Nat.le_floor_iff (by positivity : 0 ≤ τ*Real.sqrt (N:ℝ))).2 (by
    rw [mul_comm]
    exact (div_le_iff₀ hτ).1 (hP.trans hSQ))
  have hVT' : (V:ℝ) ≤ T := by exact_mod_cast hVT
  have hTV : 200*W ≤ T := by
    exact_mod_cast ((le_max_left _ _).trans (hV.le.trans hVT') :
      (200:ℝ)*(W:ℝ) ≤ (T:ℝ))
  have hStrip := (div_le_iff₀ hS).1 ((le_max_right _ _).trans (hV.le.trans hVT'))
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hSq1 : (1:ℝ) ≤ Real.sqrt (N:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  have hRoot : Real.sqrt (N:ℝ) ≤ N := by
    have hs₀ := mul_nonneg (sub_nonneg.mpr hSq1) (Real.sqrt_nonneg (N:ℝ))
    nlinarith only [hs₀,Real.sq_sqrt (show 0 ≤ (N:ℝ) by positivity)]
  have hTN : T ≤ N := by
    have hTT : (T:ℝ) ≤ τ*Real.sqrt (N:ℝ) := Nat.floor_le (by positivity)
    have hTs := mul_le_mul_of_nonneg_right hτ1 (Real.sqrt_nonneg (N:ℝ))
    have h0 : (T:ℝ) ≤ Real.sqrt (N:ℝ) := hTT.trans (by simpa only [one_mul] using hTs)
    exact_mod_cast h0.trans hRoot
  exact ⟨hnW,hTV,hTN,by linarith only [hStrip],hn0,
    by exact_mod_cast (show 2*W < N by omega),
    by exact_mod_cast hR,by exact_mod_cast hPow⟩

end ActualRayFixedWheelWindowRate318
