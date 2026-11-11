module
public import PELOriginalRegularAdditionTensor318
public import Mathlib.RingTheory.FiniteStability
public section
noncomputable section
namespace PELOriginalAdditionBasepointFree318
open scoped TensorProduct
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalProductChartPoints318 PELOriginalRegularAdditionTensor318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

instance productFiniteType : Algebra.FiniteType ℂ (ProductRing τ hτ j k) := by
  letI := PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
  letI := PELOriginalCandidateChartFiniteType318.finite_type τ hτ k
  exact Algebra.FiniteType.trans (R := ℂ) (S := CoordinateChart τ hτ j)
    (A := ProductRing τ hτ j k) inferInstance inferInstance

lemma point_factorization (f : ProductRing τ hτ j k →ₐ[ℂ] ℂ) :
    f=TensorComplexPointSeparation318.evaluation
      (f.comp Algebra.TensorProduct.includeLeft) (f.comp Algebra.TensorProduct.includeRight) := by
  apply Algebra.TensorProduct.ext
  · ext a
    simp [AlgHom.comp_apply,TensorComplexPointSeparation318.evaluation]
  · ext b
    simp [AlgHom.comp_apply,TensorComplexPointSeparation318.evaluation]

/-- The actual81 regular addition-tensor coordinates generate the unit
ideal of the ENTIRE product ring. Consequently the binary Proj map has
no base point on ANY scheme prime, not only on original complex pairs. -/
theorem span_eq_top : Ideal.span (Set.range (coordinate τ hτ j k))=⊤ := by
  by_contra h
  obtain ⟨n,φ,hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (productFiniteType τ hτ j k)
  obtain ⟨f,hf⟩ := ProperIdealComplexPoint318.exists_point φ hφ
    (Ideal.span (Set.range (coordinate τ hτ j k))) h
  have hz : (fun rs => f (coordinate τ hτ j k rs))=0 := by
    funext rs
    exact hf _ (Ideal.subset_span (Set.mem_range_self rs))
  rw [point_factorization τ hτ j k f] at hz
  exact value_vector_nonzero τ hτ j k _ _ hz
end PELOriginalAdditionBasepointFree318
