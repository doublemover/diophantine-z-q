module
public import ActualOriginalPeriodizationIntegral318
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public section
noncomputable section
namespace ActualOriginalPeriodizationCoefficient318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalCoordinateFrequency318 ActualOriginalContinuousPeriodization318
open ActualOriginalPeriodizationIntegral318 ActualOriginalTwistedWeight318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

@[expose] def integerDot (m z : Coordinates ℤ) : ℤ :=
  m.1.1*z.1.1+m.1.2*z.1.2+m.2.1.1*z.2.1.1+m.2.1.2*z.2.1.2+m.2.2*z.2.2

lemma actual_integer_frequency (m z : Coordinates ℤ) :
    frequency (integerEmbed m) (integerEmbed z) = (integerDot m z : ℝ) := by
  simp [actual_frequency_apply,dot,integerEmbed,integerDot]

lemma actual_integer_character (n : ℤ) : Real.fourierChar (n : ℝ) = 1 :=
  Circle.exp_two_pi_mul_int n

lemma actual_frequency_character_periodic (m z : Coordinates ℤ) (x : Coordinates ℝ) :
    Real.fourierChar (-frequency (integerEmbed m) (integerEmbed z+x)) =
      Real.fourierChar (-frequency (integerEmbed m) x) := by
  rw [map_add,actual_integer_frequency,neg_add,AddChar.map_add_eq_mul]
  rw [←Int.cast_neg,actual_integer_character,one_mul]

@[expose] def modulate (f : C(Coordinates ℝ,ℂ)) (m : Coordinates ℤ) : C(Coordinates ℝ,ℂ) :=
  ⟨fun x => Real.fourierChar (-frequency (integerEmbed m) x) • f x,
    (Real.continuous_fourierChar.comp (frequency (integerEmbed m)).continuous.neg).smul f.continuous⟩

lemma actual_modulate_compact (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (m : Coordinates ℤ) : HasCompactSupport (modulate f m) := hf.smul_left

lemma actual_periodization_modulate (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (m : Coordinates ℤ) (x : Coordinates ℝ) :
    periodization (modulate f m) x =
      Real.fourierChar (-frequency (integerEmbed m) x) • periodization f x := by
  rw [actual_periodization_apply _ (actual_modulate_compact f hf m),actual_periodization_apply f hf]
  simp only [modulate,ContinuousMap.coe_mk,actual_frequency_character_periodic]
  exact tsum_const_smul' _

/-- The actual periodized cube coefficient equals the original full
Fourier integral at the SAME integer frequency. This uses produced uniform
local finiteness and integral tiling, not a presumed Poisson identity. -/
theorem actual_periodized_cube_coefficient (f : C(Coordinates ℝ,ℂ))
    (hf : HasCompactSupport f) (m : Coordinates ℤ) :
    (∫ x in originalCube, Real.fourierChar (-frequency (integerEmbed m) x) • periodization f x) =
      ∫ x : Coordinates ℝ, Real.fourierChar (-frequency (integerEmbed m) x) • f x := by
  calc
    _ = ∫ x in originalCube, periodization (modulate f m) x :=
      setIntegral_congr_fun originalCube_measurable
        (fun x _ => (actual_periodization_modulate f hf m x).symm)
    _ = ∫ x : Coordinates ℝ, modulate f m x :=
      actual_original_periodization_integral _ (actual_modulate_compact f hf m)

/-- The same smooth original weight and positive quadratic phase are
used in the produced continuous periodization and in its coefficients. -/
@[expose] def actualTwistedContinuous (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) : C(Coordinates ℝ,ℂ) :=
  ⟨twistedWeight κ β W,(actual_twisted_weight_smooth κ β W hW).continuous⟩

theorem actual_original_periodization_coefficient (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (m : Coordinates ℤ) :
    (∫ x in originalCube, Real.fourierChar (-frequency (integerEmbed m) x) •
      periodization (actualTwistedContinuous κ β W hW) x) =
        originalCoordinateFourier κ β W (integerEmbed m) :=
  actual_periodized_cube_coefficient _ (actual_twisted_weight_compact κ β W hWc) m

end ActualOriginalPeriodizationCoefficient318
