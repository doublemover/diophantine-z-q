module
public import PELOriginalContinuousDeterminantCocycle318
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public section
noncomputable section
namespace PELOriginalAnalyticDeterminantCocycle318
open QuaternionicRealPeriod318 PELOriginalSiegelMatrix318 PELOriginalPeriodMatrixDerivative318
open PELOriginalFlatPeriodKernel318 PELOriginalFlatPeriodSquare318
open PELOriginalUnitFlatTransport318 PELOriginalContinuousDeterminantCocycle318
open PELOriginalDeterminantCoordinate318 PELOriginalEffectiveTensorDescent318
open PELEffectiveNormOneAction318 QuaternionicJointPeriodTopology318

lemma omega_entry_analytic (τ : ℂ) (hτ : τ≠0) (i j : Fin 2) :
    AnalyticAt ℂ (fun z=>omega z i j) τ := by
  simp only [omega_decomposition,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  exact (analyticAt_id.mul analyticAt_const).add
    ((analyticAt_id.inv hτ).mul analyticAt_const)
lemma kernel_analytic (τ : ℂ) (hτ : τ≠0) (v : ComplexVectors) :
    AnalyticAt ℂ (fun z=>kernelLift z v) τ := by
  change AnalyticAt ℂ (fun z=>(-(omega z).mulVec v,v)) τ
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.neg_apply]
  exact (AnalyticAt.pi (fun i=>(((omega_entry_analytic τ hτ i 0).mul analyticAt_const).add
    ((omega_entry_analytic τ hτ i 1).mul analyticAt_const)).neg)).prod analyticAt_const
lemma parameter_analytic (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : AnalyticAt ℂ (parameter u) τ := by
  let g := QuaternionicUnitPeriodTransport318.unitMatrix
    PELQuaternionRealRepresentation318.representation PELPrincipalOrderCoordinates318.order u.val
  change AnalyticAt ℂ (fun z=>((g 0 0:ℂ)*z+(g 0 1:ℂ))/
    ((g 1 0:ℂ)*z+(g 1 1:ℂ))) τ
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    (QuaternionicMobiusPeriods318.denominator_ne g u.property τ hτ)
lemma rawMatrix_analytic (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (i j : Fin 2) : AnalyticAt ℂ (fun z=>rawMatrix u z i j) τ := by
  let L : Ambient →L[ℂ] ℂ := (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.snd ℂ ComplexVectors ComplexVectors).comp
      (transport u.val).toContinuousLinearMap)
  exact (L.analyticAt _).comp ((kernel_analytic (parameter u τ)
    (PELOriginalSiegelNormalization318.parameter_ne _ (parameter_positive u τ hτ))
      (Pi.single i 1)).comp (parameter_analytic u τ hτ))

/-- A genuine analytic extension of the literal exterior scalar on the
upper half-plane. Its definition retains the SAME original monodromy. -/
@[expose] def rawScalar (g : effectiveGroup) (τ : ℂ) : ℂ :=
  (rawMatrix (unitLift g) τ).det
lemma rawScalar_eq (g : effectiveGroup) (τ : HalfPlane) : rawScalar g τ=scalar g τ := by
  rw [scalar_eq]
  rfl
lemma rawScalar_analytic (g : effectiveGroup) (τ : ℂ) (hτ : 0<τ.im) :
    AnalyticAt ℂ (rawScalar g) τ := by
  simp only [rawScalar,Matrix.det_fin_two]
  exact ((rawMatrix_analytic _ τ hτ 0 0).mul (rawMatrix_analytic _ τ hτ 1 1)).sub
    ((rawMatrix_analytic _ τ hτ 0 1).mul (rawMatrix_analytic _ τ hτ 1 0))
lemma rawScalar_ne (g : effectiveGroup) (τ : ℂ) (hτ : 0<τ.im) : rawScalar g τ≠0 := by
  have he := rawScalar_eq g (⟨τ,hτ⟩:HalfPlane)
  rw [he]
  exact scalar_nonzero _ _
end PELOriginalAnalyticDeterminantCocycle318
