module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public section
noncomputable section
namespace QuaternionicRealPeriod318
set_option maxHeartbeats 700000
abbrev RealMatrices := Matrix (Fin 2) (Fin 2) ℝ
abbrev ComplexVectors := Fin 2 → ℂ

/-- The period of one real matrix row against the actual vector (τ,1). -/
@[expose] def row (τ : ℂ) : (Fin 2 → ℝ) →ₗ[ℝ] ℂ where
  toFun r := (r 0:ℂ)*τ+(r 1:ℂ)
  map_add' r s := by simp only [Pi.add_apply,Complex.ofReal_add]; ring
  map_smul' a r := by
    simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,RingHom.id_apply,
      Complex.real_smul]
    ring

@[expose] def inverseRow (τ z : ℂ) : Fin 2 → ℝ :=
  ![z.im/τ.im,z.re-(z.im/τ.im)*τ.re]

theorem row_inverse (τ z : ℂ) (hτ : τ.im≠0) : row τ (inverseRow τ z)=z := by
  apply Complex.ext
  · simp only [row,LinearMap.coe_mk,AddHom.coe_mk,inverseRow,Matrix.cons_val_zero,
      Matrix.cons_val_one,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    ring
  · simp only [row,LinearMap.coe_mk,AddHom.coe_mk,inverseRow,Matrix.cons_val_zero,
      Matrix.cons_val_one,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero]
    exact div_mul_cancel₀ _ hτ

theorem inverse_row (τ : ℂ) (hτ : τ.im≠0) (r : Fin 2 → ℝ) :
    inverseRow τ (row τ r)=r := by
  funext i
  fin_cases i <;> simp only [row,LinearMap.coe_mk,AddHom.coe_mk,inverseRow,
    Matrix.cons_val_zero,Matrix.cons_val_one,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero]
  · exact mul_div_cancel_right₀ _ hτ
  · rw [mul_div_cancel_right₀ _ hτ]
    ring

/-- The real dimension is four and the complex dimension is two. This is the
period carrier for a split-real quaternion representation, not a curve's H1. -/
@[expose] def rowEquiv (τ : ℂ) (hτ : 0<τ.im) : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ :=
  { row τ with
    invFun := inverseRow τ
    left_inv := inverse_row τ hτ.ne'
    right_inv := fun z => row_inverse τ z hτ.ne' }

@[expose] def period (τ : ℂ) : RealMatrices →ₗ[ℝ] ComplexVectors where
  toFun M i := row τ (M i)
  map_add' M N := by funext i; exact (row τ).map_add (M i) (N i)
  map_smul' a M := by funext i; exact (row τ).map_smul a (M i)

@[expose] def periodEquiv (τ : ℂ) (hτ : 0<τ.im) : RealMatrices ≃ₗ[ℝ] ComplexVectors :=
  { period τ with
    invFun := fun z i => (rowEquiv τ hτ).symm (z i)
    left_inv := fun M => by funext i; exact (rowEquiv τ hτ).symm_apply_apply (M i)
    right_inv := fun z => by funext i; exact (rowEquiv τ hτ).apply_symm_apply (z i) }

@[expose] def action (g : RealMatrices) (z : ComplexVectors) : ComplexVectors :=
  fun i => (g i 0:ℂ)*z 0+(g i 1:ℂ)*z 1

/-- All left quaternionic multiplication, after the specified real splitting,
acts complex-linearly on this same period carrier. -/
theorem period_left_mul (τ : ℂ) (g M : RealMatrices) :
    period τ (g*M)=action g (period τ M) := by
  funext i
  simp only [period,row,LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_apply,Fin.sum_univ_two,
    Complex.ofReal_add,Complex.ofReal_mul,action]
  ring

@[expose] def complexStructure (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) : RealMatrices :=
  (periodEquiv τ hτ).symm (Complex.I • period τ M)

theorem period_complexStructure (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) :
    period τ (complexStructure τ hτ M)=Complex.I • period τ M :=
  (periodEquiv τ hτ).apply_symm_apply _

theorem complexStructure_square (τ : ℂ) (hτ : 0<τ.im) (M : RealMatrices) :
    complexStructure τ hτ (complexStructure τ hτ M) = -M := by
  apply (periodEquiv τ hτ).injective
  change period τ (complexStructure τ hτ (complexStructure τ hτ M))=period τ (-M)
  rw [period_complexStructure,period_complexStructure,map_neg,smul_smul,Complex.I_mul_I,
    neg_one_smul]

theorem complexStructure_commutes (τ : ℂ) (hτ : 0<τ.im) (g M : RealMatrices) :
    complexStructure τ hτ (g*M)=g*complexStructure τ hτ M := by
  apply (periodEquiv τ hτ).injective
  change period τ (complexStructure τ hτ (g*M))=period τ (g*complexStructure τ hτ M)
  rw [period_complexStructure,period_left_mul,period_left_mul,period_complexStructure]
  funext i
  simp only [Pi.smul_apply,smul_eq_mul,action]
  ring
end QuaternionicRealPeriod318
