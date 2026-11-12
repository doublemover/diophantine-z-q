module
public import ActualOriginalUniformDerivativeIntegrals318
public section
noncomputable section
namespace ActualOriginalUniformFullDualDecay318
open QuadricCRTAssembly318 ActualFullDualFourierDecay318 ActualOriginalTwistedWeight318
open ActualOriginalCoordinateFrequency318 ActualOriginalUniformDerivativeIntegrals318 MeasureTheory
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000

/-- All orders of full-dual decay with a genuinely uniform polynomial
beta loss. Constants and exponents are chosen BEFORE beta or frequency.
The function, product norm and Haar measure are exactly the original ones. -/
theorem actual_uniform_full_dual_decay (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ β : ℝ, ∀ ξ : Coordinates ℝ →L[ℝ] ℝ,
      ‖ξ‖^n * ‖originalTwistedFourier κ β W ξ‖ ≤ C*(1+‖β‖)^k := by
  obtain ⟨k,A,hA,hAint⟩ := actual_uniform_derivative_integral_bound κ W hW hWc n
  let S := Finset.range 1 ×ˢ Finset.range (n+1)
  refine ⟨k,(2:ℝ)^n*(S.card:ℝ)*A,by positivity,fun β ξ => ?_⟩
  let f := actualTwistedSchwartz κ β W hW hWc
  obtain ⟨v,hv,hξ⟩ := actual_dual_norming_vector ξ
  have hξabs : |ξ v| = ‖ξ‖ := by simpa only [Real.norm_eq_abs] using hξ
  have hf := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (dualPairing (E:=Coordinates ℝ)) (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) (f.smooth ⊤)
    (fun k j _ _ => f.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := n) (by simp) le_top v ξ
  have hbase : ‖ξ‖^n * ‖originalTwistedFourier κ β W ξ‖ ≤
      (2:ℝ)^n * ∑ p ∈ S, ∫ x : Coordinates ℝ,
        ‖x‖^p.1 * ‖iteratedFDeriv ℝ p.2 (twistedWeight κ β W) x‖ := by
    simpa only [dualPairing,ContinuousLinearMap.apply_apply,hv,hξabs,
      norm_iteratedFDeriv_zero,pow_zero,one_pow,mul_one,one_mul,Nat.cast_zero,
      zero_mul,zero_add,S,originalTwistedFourier,f,actualTwistedSchwartz] using hf
  have hsum : (∑ p ∈ S, ∫ x : Coordinates ℝ,
      ‖x‖^p.1 * ‖iteratedFDeriv ℝ p.2 (twistedWeight κ β W) x‖) ≤
      (S.card:ℝ)*(A*(1+‖β‖)^k) := by
    calc
      _ ≤ ∑ _p ∈ S, A*(1+‖β‖)^k := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : p.1=0 := by
          have h := (Finset.mem_product.mp hp).1
          simp only [Finset.mem_range] at h
          omega
        have hpn : p.2 ≤ n := by
          have h := (Finset.mem_product.mp hp).2
          simp only [Finset.mem_range] at h
          omega
        simpa only [hp0,pow_zero,one_mul] using hAint p.2 hpn β
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  calc
    _ ≤ (2:ℝ)^n * ∑ p ∈ S, ∫ x : Coordinates ℝ,
        ‖x‖^p.1 * ‖iteratedFDeriv ℝ p.2 (twistedWeight κ β W) x‖ := hbase
    _ ≤ (2:ℝ)^n*((S.card:ℝ)*(A*(1+‖β‖)^k)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Uniformity survives the proved comparison between the original
product-coordinate norm and its full dual norm. -/
theorem actual_uniform_coordinate_decay (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ β : ℝ, ∀ y : Coordinates ℝ,
      ‖y‖^n * ‖originalCoordinateFourier κ β W y‖ ≤ C*(1+‖β‖)^k := by
  obtain ⟨k,C,hC,hbound⟩ := actual_uniform_full_dual_decay κ W hW hWc n
  refine ⟨k,C,hC,fun β y => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (actual_coordinate_norm_le_dual y) n)
    (norm_nonneg _)).trans (hbound β (frequency y))

/-- On any beta window the SAME constant controls every full frequency.
The dependence on the window is explicit; no sharp stationary-phase
bound or minor-arc conclusion is asserted. -/
theorem actual_uniform_coordinate_window (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (T β : ℝ), ‖β‖ ≤ T →
      ∀ y : Coordinates ℝ,
        ‖y‖^n * ‖originalCoordinateFourier κ β W y‖ ≤ C*(1+T)^k := by
  obtain ⟨k,C,hC,hbound⟩ := actual_uniform_coordinate_decay κ W hW hWc n
  refine ⟨k,C,hC,fun T β hβ y => (hbound β y).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith) k) hC

end ActualOriginalUniformFullDualDecay318
