module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public section
noncomputable section
open scoped Matrix
namespace LinearEvaluationDeterminant318
universe u
variable {R A M ι : Type u} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable (f : A →ₗ[R] M) (b : Module.Basis ι R M) (w : ι → A)

@[expose] def columns : Matrix ι ι R := fun i j => b.equivFun (f (w j)) i

lemma combination (c : ι → R) :
    b.equivFun (f (∑ j, c j • w j)) = columns f b w *ᵥ c := by
  ext i
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec_apply_eq_sum,columns]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- An invertible determinant of actual image columns gives a genuine
surjection on the full module over ANY commutative ring. The proof uses
an explicit inverse matrix and original R-linear combinations. -/
lemma surjective (h : IsUnit (columns f b w).det) : Function.Surjective f := by
  intro y
  let c := (columns f b w)⁻¹ *ᵥ b.equivFun y
  refine ⟨∑ j,c j • w j,?_⟩
  apply b.equivFun.injective
  rw [combination]
  dsimp only [c]
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ h,Matrix.one_mulVec]
end LinearEvaluationDeterminant318
