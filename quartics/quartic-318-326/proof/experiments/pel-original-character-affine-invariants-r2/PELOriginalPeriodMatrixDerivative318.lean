module
public import PELOriginalSiegelNormalization318
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public section
noncomputable section
namespace PELOriginalPeriodMatrixDerivative318
open PELQuaternionRealRepresentation318 PELOriginalSiegelMatrix318
open PELOriginalSiegelNormalization318 QuaternionicRealPeriod318

@[expose] def linearPart : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(alpha:ℂ)/10*(3+(beta:ℂ)), -(alpha:ℂ)/10*(1+(beta:ℂ));
     -(alpha:ℂ)/10*(1+(beta:ℂ)), (alpha:ℂ)/5]
@[expose] def reciprocalPart : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(alpha:ℂ)/10*((beta:ℂ)-3), -(alpha:ℂ)/10*((beta:ℂ)-1);
     -(alpha:ℂ)/10*((beta:ℂ)-1), -(alpha:ℂ)/5]
lemma omega_decomposition (τ : ℂ) : omega τ=τ • linearPart+τ⁻¹ • reciprocalPart := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega,linearPart,reciprocalPart,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv] <;> ring

/-- The derivative of the ACTUAL normalized original period matrix,
with its full ordered integral-period basis retained. -/
@[expose] def derivative (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  linearPart+(-1/τ^2) • reciprocalPart
lemma hasDerivAt_omega (τ : ℂ) (hτ : τ≠0) : HasDerivAt omega (derivative τ) τ := by
  have h := ((hasDerivAt_id τ).smul_const linearPart).add
    (((hasDerivAt_id τ).inv hτ).smul_const reciprocalPart)
  have hf : omega=(fun z : ℂ => z • linearPart+z⁻¹ • reciprocalPart) :=
    funext omega_decomposition
  rw [hf]
  simpa only [derivative,one_smul] using h
lemma deriv_omega (τ : ℂ) (hτ : τ≠0) : deriv omega τ=derivative τ :=
  (hasDerivAt_omega τ hτ).deriv

/-- Literal a-period matrix taking normalized vectors to the SAME
original quaternionic period coordinates. -/
@[expose] def originalMatrix (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![τ,τ*(1+(beta:ℂ))/2;1,(1-(beta:ℂ))/2]
lemma originalMatrix_action (τ : ℂ) (z : ComplexVectors) :
    (originalMatrix τ).mulVec z=denormalize τ z := by
  ext i
  fin_cases i <;> simp [originalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,denormalize] <;> ring
lemma originalMatrix_det (τ : ℂ) : (originalMatrix τ).det= -(beta:ℂ)*τ := by
  simp [Matrix.det_fin_two,originalMatrix]
  ring
lemma originalMatrix_det_ne (τ : ℂ) (hτ : τ≠0) : (originalMatrix τ).det≠0 := by
  rw [originalMatrix_det]
  exact mul_ne_zero (neg_ne_zero.mpr beta_complex_ne) hτ
end PELOriginalPeriodMatrixDerivative318
