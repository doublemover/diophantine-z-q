module
public import PELOriginalUnitFlatTransport318
public import PELJointNormOneAction318
public section
noncomputable section
namespace PELOriginalFlatPeriodSquare318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 PELOriginalSiegelNormalization318
open PELOriginalFlatPeriodKernel318 PELOriginalComplexifiedOrder318
open PELOriginalUnitFlatTransport318 QuaternionicMobiusPeriods318
open QuaternionicUnitPeriodTransport318

@[expose] def matrixPeriod (τ : ℂ) (M : Mat) : QuaternionicRealPeriod318.ComplexVectors :=
  M.mulVec ![τ,1]
lemma split_period (τ : ℂ) (hτ : τ≠0) (p : Ambient) :
    matrixPeriod τ (split p)=denormalize τ (periodMap τ p) := by
  ext i
  fin_cases i <;>
    simp [matrixPeriod,split,periodMap,denormalize,PELOriginalSiegelMatrix318.omega,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hτ] <;> ring_nf <;> simp only [beta_complex_sq] <;> ring

lemma matrixPeriod_mobius (g : RealMatrices) (τ : ℂ) (hd : denominator g τ≠0) (M : Mat) :
    matrixPeriod (mobius g τ) M=(denominator g τ)⁻¹ •
      matrixPeriod τ (M*(fun i j => (g i j:ℂ))) := by
  ext i
  simp [matrixPeriod,mobius,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two,
    smul_eq_mul]
  field_simp [hd]
  unfold denominator
  ring

variable (u : PELJointNormOneAction318.normOneUnits) (τ : ℂ) (hτ : 0<τ.im)
@[expose] def parameter : ℂ := unitParameter representation order u.val τ
include hτ in
lemma parameter_positive : 0<(parameter u τ).im := mobius_positive _ u.property τ hτ
include hτ in
lemma denominator_ne : unitDenominator representation order u.val τ≠0 :=
  QuaternionicMobiusPeriods318.denominator_ne _ u.property τ hτ

include hτ in
/-- Whole original-coordinate period square under the actual constant
right-unit automorphism. The automorphy denominator is retained exactly. -/
lemma original_period_square (p : Ambient) :
    denormalize τ (periodMap τ (transport u.val p))=
      unitDenominator representation order u.val τ •
        denormalize (parameter u τ) (periodMap (parameter u τ) p) := by
  rw [←split_period τ (parameter_ne τ hτ),split_transport,
    ←split_period (parameter u τ) (parameter_ne _ (parameter_positive u τ hτ))]
  have h := matrixPeriod_mobius (unitMatrix representation order u.val) τ
    (denominator_ne u τ hτ) (split p)
  change matrixPeriod (parameter u τ) (split p)=
    (unitDenominator representation order u.val τ)⁻¹ •
      matrixPeriod τ (split p*unitMatrixC u.val) at h
  rw [h,smul_smul,mul_inv_cancel₀ (denominator_ne u τ hτ),one_smul]

/-- Genuine quotient-space gauge produced from the actual two period
normalizations and the exact nonzero automorphy factor. -/
@[expose] def quotientGauge : ComplexVectors ≃ₗ[ℂ] ComplexVectors :=
  (normalization (parameter u τ) (parameter_positive u τ hτ)).symm.trans
    ((scalarEquiv (unitDenominator representation order u.val τ)
      (denominator_ne u τ hτ)).symm.trans (normalization τ hτ))
lemma period_square (p : Ambient) :
    periodMap τ (transport u.val p)=quotientGauge u τ hτ (periodMap (parameter u τ) p) := by
  apply (normalization τ hτ).symm.injective
  change denormalize τ (periodMap τ (transport u.val p))=
    denormalize τ (normalize τ
      (unitDenominator representation order u.val τ •
        denormalize (parameter u τ) (periodMap (parameter u τ) p)))
  rw [denormalize_normalize τ hτ]
  exact original_period_square u τ hτ p

include hτ in
/-- Exact all-vector equivalence between the two actual period kernels. -/
theorem kernel_transport (p : Ambient) :
    periodMap τ (transport u.val p)=0 ↔ periodMap (parameter u τ) p=0 := by
  rw [period_square u τ hτ]
  exact (quotientGauge u τ hτ).map_eq_zero_iff
end PELOriginalFlatPeriodSquare318
