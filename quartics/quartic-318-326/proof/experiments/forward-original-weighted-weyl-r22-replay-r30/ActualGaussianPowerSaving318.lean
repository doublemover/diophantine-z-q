module
public import ActualGaussianThresholdTail318
public section
noncomputable section
namespace ActualGaussianPowerSaving318
open ActualGaussianTwoChartTail318 ActualGaussianThresholdTail318 ActualGaussianLogBudget318
open OriginalUniformEulerRankin318 OriginalGlobalBadMass318 OriginalBadSliceLogWeight318
set_option maxHeartbeats 12000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A genuine fixed-kappa/delta constant. No dependence on source B,
sieve cutoffY, source label, or chosen lattice is hidden here. -/
@[expose] def rankinCoefficient (κ : ℤ) (δ : ℝ) : ℝ :=
  2*rankinConstant κ δ*(2:ℝ)^δ

lemma rankin_power (κ : ℤ) (δ : ℝ) (B : ℕ) (hB : 1≤B) (a : ℝ) :
    (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*(B:ℝ)^a=
      rankinCoefficient κ δ*(B:ℝ)^(a+δ) := by
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hb.le,Real.rpow_add hb]
  dsimp [rankinCoefficient]
  ring

lemma threshold_product (B : ℕ) (hB : 1≤B) :
    (B:ℝ)^2*threshold B=(B:ℝ)^((11:ℝ)/4) := by
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have he : (11:ℝ)/4=2+(3:ℝ)/4 := by norm_num
  rw [he,Real.rpow_add hb]
  norm_num [threshold,Real.rpow_natCast]

/-- Explicit optimized original-source upper bound. This exhibits the
B^(3+delta)/Y and B^(11/4+delta) terms with only the constructed logarithmic
height envelope. It is NOT a prime-pattern existence theorem and does not
silently add the missing zero/both-label strata to the counted source. -/
@[expose] def optimizedBudget (κ : ℤ) (δ : ℝ) (B Y : ℕ) : ℝ :=
  rankinCoefficient κ δ*113246208*(B:ℝ)^((3:ℝ)+δ)/(Y:ℝ)+
    (rankinCoefficient κ δ*(25930800*logEnvelope κ B/Real.log (Y:ℝ)+25401600)+
      2*tailConstant δ)*(B:ℝ)^((11:ℝ)/4+δ)

theorem actual_original_power_saving (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 3≤Y) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    twoChartMass B κ Y γ≤weightCeiling B γ*optimizedBudget κ δ B Y := by
  have hYR : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hl : 0<Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have hh := actual_threshold_tail B hB κ hκ Y hY γ δ hδ
  have h3 := rankin_power κ δ B hB 3
  rw [Real.rpow_natCast] at h3
  have hq := rankin_power κ δ B hB ((11:ℝ)/4)
  rw [←threshold_product B hB] at hq
  let C := 2*rankinConstant κ δ*(2*(B:ℝ))^δ
  have he :
      C*combinedBudget κ B (threshold B) Y*weightCeiling B γ+
        2*tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*weightCeiling B γ*Real.log (Y:ℝ)=
      (weightCeiling B γ*optimizedBudget κ δ B Y)*Real.log (Y:ℝ) := by
    change C*(B:ℝ)^3=rankinCoefficient κ δ*(B:ℝ)^((3:ℝ)+δ) at h3
    change C*((B:ℝ)^2*threshold B)=rankinCoefficient κ δ*(B:ℝ)^((11:ℝ)/4+δ) at hq
    calc
      _ = weightCeiling B γ*(113246208*(C*(B:ℝ)^3)/(Y:ℝ)*Real.log (Y:ℝ)+
          (25930800*logEnvelope κ B+25401600*Real.log (Y:ℝ))*
            (C*((B:ℝ)^2*threshold B))+
          2*tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*Real.log (Y:ℝ)) := by
        dsimp [combinedBudget]
        ring
      _ = _ := by
        rw [h3,hq]
        dsimp [optimizedBudget]
        field_simp [ne_of_gt hYR,ne_of_gt hl]
        <;> ring
  exact (mul_le_mul_right hl).mp (hh.trans_eq he)

end ActualGaussianPowerSaving318
