module
public import ActualOriginalTorusFourierCoefficient318
public section
noncomputable section
namespace ActualOriginalPoissonSummation318
open QuadricCRTAssembly318 ActualOriginalCoordinateIndex318 ActualOriginalTorusPeriodization318
open ActualOriginalTorusFourierCoefficient318 ActualOriginalCompactFourier318
open ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalTwistedWeight318
open scoped BigOperators ContDiff
set_option maxHeartbeats 16000000

lemma actual_original_torus_coefficient_summable (f : C(Coordinates ℝ,ℂ))
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Summable (UnitAddTorus.mFourierCoeff (torusPeriodization f hc)) := by
  have hs := (actual_compact_fourier_lattice_summable f hf hc).2
  have hi := hs.comp_injective (coordinateEquiv ℤ).injective
  simpa only [actual_torus_fourier_coefficient f hc] using hi

/-- Actual five-dimensional Poisson summation in the ORIGINAL product
norm/Haar and literal integer lattice. Both torus descent and coefficients,
and absolute dual-lattice summability, have been produced before inversion. -/
theorem actual_original_poisson (f : Coordinates ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∑' z : Coordinates ℤ, f (integerEmbed z)) =
      ∑' z : Coordinates ℤ, compactFourier f (integerEmbed z) := by
  let F : C(Coordinates ℝ,ℂ) := ⟨f,hf.continuous⟩
  have hF : ContDiff ℝ ∞ F := hf
  have hFc : HasCompactSupport F := hc
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (actual_original_torus_coefficient_summable F hF hFc) (0 : UnitAddTorus Index)
  have hm (n : Index → ℤ) : UnitAddTorus.mFourier n (0 : UnitAddTorus Index)=1 := by
    simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.zero_apply,
      fourier_eval_zero,Finset.prod_const_one]
  simp only [hm,smul_eq_mul,mul_one] at hs
  calc
    (∑' z : Coordinates ℤ, f (integerEmbed z)) = torusPeriodization F hFc 0 :=
      (actual_torus_periodization_zero F hFc).symm
    _ = ∑' n : Index → ℤ, UnitAddTorus.mFourierCoeff (torusPeriodization F hFc) n :=
      hs.tsum_eq.symm
    _ = ∑' n : Index → ℤ, compactFourier F (integerEmbed (coordinateEquiv ℤ n)) :=
      tsum_congr (actual_torus_fourier_coefficient F hFc)
    _ = ∑' z : Coordinates ℤ, compactFourier f (integerEmbed z) :=
      (coordinateEquiv ℤ).toEquiv.tsum_eq (fun z => compactFourier f (integerEmbed z))

/-- Concrete circle-method input: SAME original real weight W, SAME
positive quadratic phase and SAME full negative Fourier character. This is
an exact fixed-beta Poisson identity, not a uniform major/minor arc estimate. -/
theorem actual_original_twisted_poisson (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    (∑' z : Coordinates ℤ, twistedWeight κ β W (integerEmbed z)) =
      ∑' z : Coordinates ℤ, originalCoordinateFourier κ β W (integerEmbed z) := by
  exact actual_original_poisson (twistedWeight κ β W)
    (actual_twisted_weight_smooth κ β W hW) (actual_twisted_weight_compact κ β W hWc)

end ActualOriginalPoissonSummation318
