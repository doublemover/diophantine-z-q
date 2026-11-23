module
public import OriginalMarkedHodgeTensorHeight318
public import SelectedActualSameACurvature64
public section
noncomputable section

namespace OriginalMarkedHeightCalibration318

open NumberField OriginalGlobalHodgeIdealHeight318
open scoped TensorProduct

/-- Exactly the absolute value of the literal denominator T(T−32)(T+343)(T−76832). -/
@[expose] def denominator (z : ℂ) : ℝ :=
  ‖z‖ * ‖z - (32 : ℂ)‖ * ‖z - (-343 : ℂ)‖ * ‖z - (76832 : ℂ)‖

/-- One infinite place of the same marked point, on the ordinary normalized coordinate.
The compact weighted-metric comparison, the actual Faltings period computation,
and the absolute value of the actual raw determinant quotient are inputs;
the cutoff, the archive's U, and its f are not. The scalar is not taken from a
separately chosen frame, and replacing raw Ψ by Ψ/210 changes raw_norm. -/
structure AtPlace (z : ℂ) (scalar hodgeNorm : ℝ) where
  derivativeNorm : ℝ
  imaginary : ℝ
  periodNorm : ℝ
  derivative_pos : 0 < derivativeNorm
  imaginary_pos : 0 < imaginary
  period_pos : 0 < periodNorm
  noncontact : 0 < denominator z
  compact_read :
    64 * (SelectedActualSameACurvature64.metricU z * derivativeNorm ^ 2 * imaginary ^ 2) ≤
      denominator z
  hodge_sq :
    hodgeNorm ^ 2 = 210 * periodNorm ^ 2 * imaginary ^ 2 / Real.pi ^ 2
  raw_norm :
    scalar = derivativeNorm ^ 2 / denominator z * (2 * Real.pi) ^ 2 /
      (210 * periodNorm ^ 2)

/-- The exact calibrated architecture used by the finite tensor receiver.
This inserts no comparison assumption about unrelated X or A. -/
theorem at_place_bound {z : ℂ} {c a : ℝ} (R : AtPlace z c a) :
    ∃ U f : ℝ, 2 * max 32 ‖z‖ ≤ U ∧ 64 ≤ f ∧ c * a ^ 2 = 4 / (U * f) := by
  let U := SelectedActualSameACurvature64.metricU z
  have hU0 : 2 * max 32 ‖z‖ ≤ U := SelectedActualSameACurvature64.sourceU_lower z
  have hU : 0 < U := by linarith [le_max_left (32 : ℝ) ‖z‖]
  have hd : 0 < R.derivativeNorm ^ 2 := pow_pos R.derivative_pos _
  have hy : 0 < R.imaginary ^ 2 := pow_pos R.imaginary_pos _
  have hden : 0 < U * R.derivativeNorm ^ 2 * R.imaginary ^ 2 :=
    mul_pos (mul_pos hU hd) hy
  let f := denominator z / (U * R.derivativeNorm ^ 2 * R.imaginary ^ 2)
  refine ⟨U, f, hU0, (le_div_iff₀ hden).mpr R.compact_read, ?_⟩
  rw [R.raw_norm, R.hodge_sq]
  dsimp only [f]
  have hper : R.periodNorm ≠ 0 := R.period_pos.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [R.noncontact.ne', R.derivative_pos.ne', R.imaginary_pos.ne',
    hU.ne', hper, hpi]
  ring

variable {F : Type*} [Field F] [NumberField F]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite (𝓞 F) M]

/-- Backward consumer on one global Hodge module, two actual integral square
tensors, their literal generic readback, and the same-place raw determinant
and metric comparison. The original family/chart must supply these data. -/
theorem height_of_marked_calibrations {S₃ S₁₁ : Type*} [CommRing S₃] [CommRing S₁₁]
    [Algebra (𝓞 F) S₃] [Algebra S₃ F] [IsScalarTower (𝓞 F) S₃ F]
    [Algebra (𝓞 F) S₁₁] [Algebra S₁₁ F] [IsScalarTower (𝓞 F) S₁₁ F]
    [IsLocalization.Away (3 : 𝓞 F) S₃] [IsLocalization.Away (11 : 𝓞 F) S₁₁]
    (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F)
    (Z3 : Fin 2 → S₃ ⊗[𝓞 F] (M ⊗[𝓞 F] M))
    (Z11 : Fin 2 → S₁₁ ⊗[𝓞 F] (M ⊗[𝓞 F] M))
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) (t : ℚ) (c : F) (hc : c ≠ 0)
    (gen3 : ∀ i, OriginalMarkedHodgeTensorHeight318.openRead S₃ e (Z3 i) =
      hodgeCoefficient t c i)
    (gen11 : ∀ i, OriginalMarkedHodgeTensorHeight318.openRead S₁₁ e (Z11 i) =
      hodgeCoefficient t c i)
    (R : ∀ w : InfinitePlace F, AtPlace (w.embedding (t : F)) (w.val c) (A w)) :
    Height.logHeight₁ (t / 32) <
      2 * (idealFrame (OriginalMarkedHodgeTensorHeight318.integralIdeal e)
        (OriginalMarkedHodgeTensorHeight318.integralIdeal_ne_zero e) A hA).normalizedDegree + 11 := by
  apply OriginalMarkedHodgeTensorHeight318.height_of_original_marked_tensors
    e Z3 Z11 A hA t c hc gen3 gen11
  intro w
  have hp := at_place_bound (R w)
  rw [InfinitePlace.norm_embedding_eq] at hp
  exact hp

end OriginalMarkedHeightCalibration318

#print axioms OriginalMarkedHeightCalibration318.at_place_bound
#print axioms OriginalMarkedHeightCalibration318.height_of_marked_calibrations
