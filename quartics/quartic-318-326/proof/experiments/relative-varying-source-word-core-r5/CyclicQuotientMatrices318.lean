module
public import CyclicQuotientKernel318
public import Mathlib.LinearAlgebra.Matrix.ToLin
public section
noncomputable section
namespace CyclicQuotientMatrices318
open CyclicQuotientEvaluation318
universe u
variable {R A M ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable (ρ : A →ₐ[R] Module.End R M) (v : M) (b : Basis ι R M)

@[expose] def matrix (a : A) : Matrix ι ι R := LinearMap.toMatrix b b (ρ a)
@[expose] def vector : ι → R := b.repr v

lemma matrix_mul (a c : A) : matrix ρ b (a*c) = matrix ρ b a * matrix ρ b c := by
  unfold matrix
  rw [map_mul,LinearMap.toMatrix_mul]

lemma matrix_one : matrix ρ b 1 = 1 := by
  unfold matrix
  rw [map_one,LinearMap.toMatrix_one]

/-- Commutativity is an actual matrix identity over the original arbitrary
coefficient ring, retaining nilpotents and not just geometric points. -/
lemma matrix_commute (a c : A) : matrix ρ b a * matrix ρ b c =
    matrix ρ b c * matrix ρ b a := by
  rw [← matrix_mul,← matrix_mul,mul_comm a c]

lemma matrix_vector (a : A) : matrix ρ b a *ᵥ vector v b = b.repr (evaluation ρ v a) :=
  LinearMap.toMatrix_mulVec_repr b b (ρ a) v

lemma matrix_vector_zero_iff (a : A) :
    matrix ρ b a *ᵥ vector v b = 0 ↔ a ∈ ideal ρ v := by
  rw [matrix_vector]
  constructor
  · intro h
    change evaluation ρ v a = 0
    apply b.repr.injective
    ext i
    have hi := congrFun h i
    simpa only [map_zero,Finsupp.zero_apply,Pi.zero_apply] using hi
  · intro h
    change evaluation ρ v a = 0 at h
    rw [h,map_zero]

/-- The original cyclic-surjectivity condition becomes surjectivity of
the actual matrix/vector evaluation on all vectors over R. -/
lemma matrix_vector_surjective (h : Function.Surjective (evaluation ρ v)) :
    Function.Surjective (fun a => matrix ρ b a *ᵥ vector v b) := by
  intro w
  obtain ⟨a,ha⟩ := h (b.equivFun.symm w)
  refine ⟨a,?_⟩
  rw [matrix_vector,ha]
  change b.equivFun (b.equivFun.symm w) = w
  exact b.equivFun.apply_symm_apply w
end CyclicQuotientMatrices318
