module
public import PELOriginalDeterminantalMonodromy318
public import PELOriginalDeterminantCover318
public section
noncomputable section
namespace PELOriginalContinuousDeterminantCocycle318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 PELEffectiveNormOneAction318
open PELOriginalFlatPeriodKernel318 PELOriginalFlatPeriodSquare318
open PELOriginalKernelMonodromyCovariance318 PELOriginalUnitFlatTransport318
open PELOriginalFlatSymplecticTransport318 PELOriginalEffectiveTensorDescent318
open PELOriginalDeterminantCoordinate318 PELOriginalKernelDeterminantLine318
open scoped Topology

@[expose] def rawMatrix (u : PELJointNormOneAction318.normOneUnits) (τ : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (transport u.val (kernelLift (parameter u τ) (Pi.single i 1))).2 j
lemma rawMatrix_continuousAt (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (i j : Fin 2) :
    ContinuousAt (fun z=>rawMatrix u z i j) τ := by
  have hγ := MobiusPoincarePullback318.hasDerivAt_mobius
    (QuaternionicUnitPeriodTransport318.unitMatrix PELQuaternionRealRepresentation318.representation
      PELPrincipalOrderCoordinates318.order u.val) u.property τ hτ
  have hk := (PELOriginalPeriodKernelConnection318.hasDerivAt_kernelLift (parameter u τ)
    (PELOriginalSiegelNormalization318.parameter_ne _ (parameter_positive u τ hτ))
    (Pi.single i 1)).scomp τ hγ
  have ht := hasDerivAt_transport u _ _ τ hk
  exact (continuous_apply j).continuousAt.comp ht.continuousAt.snd

@[expose] def scalar (g : effectiveGroup) (τ : HalfPlane) : ℂ :=
  coefficient (PELOriginalDeterminantDescent318.transition g τ generator)
lemma scalar_eq (g : effectiveGroup) (τ : HalfPlane) :
    scalar g τ=transitionScalar (unitLift g) τ τ.property :=
  coefficient_transition_generator _ _ _
lemma scalar_nonzero (g : effectiveGroup) (τ : HalfPlane) : scalar g τ≠0 := by
  rw [scalar_eq]
  exact transitionScalar_ne _ _ _
lemma scalar_on_line (g : effectiveGroup) (τ : HalfPlane) (x : Coordinates) :
    coefficient (PELOriginalDeterminantDescent318.transition g τ x)=scalar g τ*coefficient x := by
  rw [scalar_eq]
  exact coefficient_transition _ _ _ x
lemma scalar_one (τ : HalfPlane) : scalar 1 τ=1 := by
  rw [scalar,PELOriginalDeterminantDescent318.identity]
  exact coefficient_generator
lemma scalar_cocycle (g h : effectiveGroup) (τ : HalfPlane) :
    scalar h τ*scalar g (h • τ)=scalar (g*h) τ := by
  have he := congrArg (fun e : Coordinates ≃ₗ[ℂ] Coordinates=>coefficient (e generator))
    (PELOriginalDeterminantDescent318.cocycle g h τ)
  change coefficient (PELOriginalDeterminantDescent318.transition h τ
    (PELOriginalDeterminantDescent318.transition g (h • τ) generator))=_ at he
  rw [scalar_on_line] at he
  exact he

/-- Continuity of the literal determinant coefficient, obtained from the
actual differentiable original period maps and constant integral transport. -/
lemma scalar_continuous (g : effectiveGroup) : Continuous (scalar g) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  have he : scalar g=(fun t : HalfPlane=>(rawMatrix (unitLift g) t).det) := by
    funext t
    rw [scalar_eq]
    rfl
  rw [he]
  have h (i j : Fin 2) : ContinuousAt (fun t : HalfPlane=>rawMatrix (unitLift g) t i j) τ :=
    (rawMatrix_continuousAt _ τ τ.property i j).comp continuous_subtype_val.continuousAt
  simp only [Matrix.det_fin_two]
  exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
end PELOriginalContinuousDeterminantCocycle318
