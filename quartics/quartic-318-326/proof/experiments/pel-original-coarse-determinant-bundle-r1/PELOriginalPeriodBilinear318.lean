module
public import PELOriginalPeriodDerivativeCongruence318
public import PELOriginalHermitianCoordinates318
public section
noncomputable section
namespace PELOriginalPeriodBilinear318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELOriginalSiegelNormalization318 PELOriginalPeriodMatrixDerivative318
open PELOriginalPeriodDerivativeCongruence318 PELOriginalHermitianCoordinates318

/-- Actual bilinear period derivative after the literal original a-period
coordinate congruence. It is defined on ALL original complex vectors. -/
@[expose] def pairing (τ : ℂ) (z w : ComplexVectors) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    z i*(originalMatrix τ*derivative τ*(originalMatrix τ).transpose) i j*w j
lemma pairing_formula (τ : ℂ) (hτ : τ≠0) (z w : ComplexVectors) :
    pairing τ z w=(alpha:ℂ)*(z 0*w 0+z 1*w 1) := by
  unfold pairing
  rw [original_congruence τ hτ]
  simp [Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Full comparison with the actual original polarization Hermitian form,
including cross vectors, retaining the literal factor210 and Im(tau)^2.
This proves a coordinate identity, not a relative Gauss-Manin identification. -/
lemma original_hermitian_comparison (τ : ℂ) (hτ : 0<τ.im) (z w : ComplexVectors) :
    (τ.im:ℂ)*pairing τ z (fun i => star (w i))=
      (210:ℂ)*(τ.im:ℂ)^2*PELOriginalHermitianForm318.form τ hτ z w := by
  rw [pairing_formula τ (parameter_ne τ hτ),form_coordinates]
  have ha : (alpha:ℂ)≠0 := by exact_mod_cast alpha_pos.ne'
  have hy : (τ.im:ℂ)≠0 := by exact_mod_cast hτ.ne'
  push_cast
  field_simp [ha,hy]
  ring_nf
  rw [alpha_complex_sq]
  ring
end PELOriginalPeriodBilinear318
