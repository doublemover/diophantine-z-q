module
public import VaryingMatrixWords318
public import VaryingQuotientMatrixCoordinates318
public import LinearEvaluationDeterminant318
public section
noncomputable section
namespace OriginalWordBasisCyclicity318
open CyclicQuotientEvaluation318 VaryingMatrixWords318 VaryingQuotientMatrixCoordinates318
universe u
variable {R A M σ ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable (ρ : A →ₐ[R] Module.End R M) (v : M) (b : Module.Basis ι R M) (g : σ → A)

/-- The universal word columns are the coordinates of the SAME original
source-algebra products acting on the SAME vector. -/
lemma wordVector_original (l : List σ) :
    wordVector (data ρ v b g) l = b.equivFun (evaluation ρ v (l.map g).prod) := by
  induction l with
  | nil =>
    change b.equivFun v = b.equivFun (ρ 1 v)
    exact congrArg (fun a : Module.End R M => b.equivFun (a v)) (map_one ρ).symm
  | cons s l ih =>
    change CyclicQuotientMatrices318.matrix ρ b (g s) *ᵥ
      wordVector (data ρ v b g) l =
      b.equivFun (evaluation ρ v (g s * (l.map g).prod))
    rw [ih,evaluation_mul]
    exact LinearMap.toMatrix_mulVec_repr b b (ρ (g s)) (evaluation ρ v (l.map g).prod)

/-- A chosen tuple of finite words with invertible actual determinant
DISCHARGES cyclic-surjectivity, rather than taking it as an extra chart
premise. No field, reducedness or set-of-points argument is used. -/
lemma cyclic (w : ι → List σ)
    (h : IsUnit (determinant (data ρ v b g) w)) :
    Function.Surjective (evaluation ρ v) := by
  apply LinearEvaluationDeterminant318.surjective (evaluation ρ v) b
    (fun j => ((w j).map g).prod)
  have hc : LinearEvaluationDeterminant318.columns (evaluation ρ v) b
      (fun j => ((w j).map g).prod) = columns (data ρ v b g) w := by
    ext i j
    exact congrFun (wordVector_original ρ v b g (w j)).symm i
  rw [hc]
  exact h
end OriginalWordBasisCyclicity318
