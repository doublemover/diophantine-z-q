module
public import SelectedWholeOrdinaryPeriodEvaluation318
public import SelectedActualAdmissiblePeriodPath318
public section
noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedPrimitiveSameRootEvaluation318 OpenJComplexEvaluation318
open SelectedMarkedPeriodCoordinate318

namespace SelectedWholeOrdinaryPath318

/-- The topology is the induced topology in the two literal complex
coordinates, not an arbitrary topology on the RingHom type. -/
@[expose] def evaluationCoordinates (N : ℕ) (p : (R N)[X])
    (f : AdjoinRoot p →+* ℂ) : ℂ × ℂ :=
  (f (algebraMap (R N) (AdjoinRoot p) (OpenJModel318.jCoord N)),
    f (AdjoinRoot.root p))

@[expose] def periodCoordinates (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : ℂ × ℂ :=
  (ActualQJ318.jInvariant τ,arithmeticX N τ)

theorem continuous_periodCoordinates (N : ℕ) [NeZero N] (hN : 1 < N) :
    ContinuousOn (periodCoordinates N) {τ : UpperHalfPlane | Admissible τ} := by
  intro τ hτ
  have hc := ((OpenJLocalComparison318.j_analyticAt τ).prod
    (arithmeticX_analyticAt N hN τ hτ)).continuousAt
  have hc' := hc.comp UpperHalfPlane.continuous_coe.continuousAt
  apply ContinuousAt.continuousWithinAt
  simpa only [Function.comp_def,OpenJLocalComparison318.j,
    UpperHalfPlane.ofComplex_apply,periodCoordinates] using hc'

variable (N : ℕ) [NeZero N] [IsFinite (kernelProjection N N)]
  [Etale (kernelProjection N N)]
variable (hN : 2 < N) (I : Ideal (D N))
variable (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I)))
variable (hb : primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I))
variable (he : intoAffine N N (by omega : 1 < N) =
  e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
variable (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
variable (hσ : σ.comp (q N I) = (q N I).comp (sign N))
variable (p : (R N)[X]) (ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ)
variable (hep : ep (AdjoinRoot.root p) = coordinate N I σ hσ)

include hN hb he hσ hep in
theorem rootEval_coordinates (τ : UpperHalfPlane) (hτ : Admissible τ) :
    evaluationCoordinates N p (rootEval N I e hb τ hτ σ p ep) = periodCoordinates N τ := by
  apply Prod.ext
  · change rootEval N I e hb τ hτ σ p ep
      (algebraMap (R N) (AdjoinRoot p) (OpenJModel318.jCoord N)) = ActualQJ318.jInvariant τ
    rw [rootEval_base,evaluation_jCoord]
  · exact rootEval_root N I e hb τ hτ σ hσ p ep hep (by omega) he

include hN hb he hσ hep in
theorem whole_chart_image :
    periodCoordinates N '' {τ : UpperHalfPlane | Admissible τ} =
      Set.range (evaluationCoordinates N p) := by
  ext x
  constructor
  · rintro ⟨τ,hτ,rfl⟩
    exact ⟨rootEval N I e hb τ hτ σ p ep,
      rootEval_coordinates N hN I e hb he σ hσ p ep hep τ hτ⟩
  · rintro ⟨f,rfl⟩
    obtain ⟨τ,hτ,hf⟩ := SelectedWholeOrdinaryPeriodEvaluation318.point_surjective
      N hN I e hb he σ hσ p ep hep f
    exact ⟨τ,hτ,(rootEval_coordinates N hN I e hb he σ hσ p ep hep τ hτ).symm.trans
      (congrArg (evaluationCoordinates N p) hf)⟩

/-- The entire complex point locus of this same monogenic primitive
chart is path connected in its literal (J,x) coordinates. No
arbitrary preselected connected component of a scalar lift is used. -/
include hN hb he hσ hep in
theorem whole_chart_pathConnected :
    IsPathConnected (Set.range (evaluationCoordinates N p)) := by
  rw [← whole_chart_image N hN I e hb he σ hσ p ep hep]
  exact SelectedActualAdmissiblePeriodPath318.admissible_pathConnected.image'
    (continuous_periodCoordinates N (by omega))

end SelectedWholeOrdinaryPath318

#print axioms SelectedWholeOrdinaryPath318.whole_chart_image
#print axioms SelectedWholeOrdinaryPath318.whole_chart_pathConnected
