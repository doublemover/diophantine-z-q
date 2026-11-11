module
public import ActualOriginalCompactFourier318
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public section
noncomputable section
namespace ActualOriginalTorusFourierCoefficient318
open QuadricCRTAssembly318 ActualOriginalCoordinateIndex318 ActualOriginalTorusPeriodization318
open ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalContinuousPeriodization318 ActualOriginalPeriodizationCoefficient318
open ActualOriginalCompactFourier318 MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_scalar_fourier_character (n : ℤ) (x : ℝ) :
    fourier n (x : UnitAddCircle) = (Real.fourierChar ((n : ℝ)*x) : ℂ) := by
  rw [fourier_coe_apply,Real.fourierChar_apply]
  simp only [Complex.ofReal_one,div_one]
  push_cast
  congr 1
  ring

lemma actual_multifourier_pullback (n : Index → ℤ) (x : Index → ℝ) :
    UnitAddTorus.mFourier n (torusQuotient x) =
      (Real.fourierChar (∑ i : Index, (n i : ℝ)*x i) : ℂ) := by
  classical
  have hs (s : Finset Index) :
      (∏ i ∈ s, (Real.fourierChar ((n i : ℝ)*x i) : ℂ)) =
        (Real.fourierChar (∑ i ∈ s, (n i : ℝ)*x i) : ℂ) := by
    induction s using Finset.induction with
    | empty => simp only [Finset.prod_empty,Finset.sum_empty,AddChar.map_zero_eq_one,Circle.coe_one]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,AddChar.map_add_eq_mul,Circle.coe_mul]
  simpa only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,torusQuotient,
    actual_scalar_fourier_character] using hs Finset.univ

lemma actual_negative_multifourier (n : Index → ℤ) (x : Index → ℝ) :
    UnitAddTorus.mFourier (-n) (torusQuotient x) =
      (Real.fourierChar (-frequency (integerEmbed (coordinateEquiv ℤ n)) (coordinateEquiv ℝ x)) : ℂ) := by
  rw [actual_multifourier_pullback,actual_frequency_apply,←actual_coordinate_index_integer,
    actual_coordinate_index_dot]
  simp only [Pi.neg_apply,Int.cast_neg,neg_mul,Finset.sum_neg_distrib]

@[expose] def originalIocCube : Set (Coordinates ℝ) :=
  (Ioc (0 : ℝ) 1 ×ˢ Ioc 0 1) ×ˢ (Ioc 0 1 ×ˢ Ioc 0 1) ×ˢ Ioc 0 1

/-- The Fourier-series API uses Ioc while original tiling uses Ico.
Their difference is actually null in the SAME original product volume. -/
lemma actual_original_cube_boundary : originalIocCube =ᵐ[volume] originalCube := by
  have h : Ioc (0 : ℝ) 1 =ᵐ[(volume : Measure ℝ)] Ico 0 1 :=
    (Ico_ae_eq_Ioc' (by simp) (by simp)).symm
  exact set_prod_ae_eq (set_prod_ae_eq h h) (set_prod_ae_eq (set_prod_ae_eq h h) h)

lemma actual_index_ioc_preimage :
    (coordinateEquiv ℝ) ⁻¹' originalIocCube = {x : Index → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
  ext x
  simp [originalIocCube,actual_coordinate_index_apply,Sum.forall,Fin.forall_fin_two]

/-- The actual torus coefficient is exactly the original full Fourier
integral at the corresponding integer frequency. Product Haar transport and
the Ioc/Ico null-boundary conversion are explicit. -/
theorem actual_torus_fourier_coefficient (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (n : Index → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f hf) n =
      compactFourier f (integerEmbed (coordinateEquiv ℤ n)) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusPeriodization f hf) n (0 : Index → ℝ)]
  simp only [Pi.zero_apply,zero_add]
  change (∫ x in {x : Index → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1},
    UnitAddTorus.mFourier (-n) (torusQuotient x) •
      torusPeriodization f hf (torusQuotient x)) = _
  simp_rw [actual_negative_multifourier,actual_torus_periodization_pullback]
  change (∫ x in {x : Index → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1},
    Real.fourierChar (-frequency (integerEmbed (coordinateEquiv ℤ n)) (coordinateEquiv ℝ x)) •
      periodization f (coordinateEquiv ℝ x)) = _
  rw [←actual_index_ioc_preimage]
  rw [actual_coordinate_index_measure_preserving.setIntegral_preimage_emb
    (coordinateEquiv ℝ).measurableEmbedding
    (fun x => Real.fourierChar (-frequency (integerEmbed (coordinateEquiv ℤ n)) x) • periodization f x)
    originalIocCube]
  rw [setIntegral_congr_set actual_original_cube_boundary]
  exact actual_periodized_cube_coefficient f hf (coordinateEquiv ℤ n)

end ActualOriginalTorusFourierCoefficient318
