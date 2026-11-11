module
public import VaryingSourceGeneratorSpan318
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public section
noncomputable section
namespace VaryingSourceLocalWordCover318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingSourceGeneratorSpan318 VaryingSourceWordQuotient318
open VaryingMatrixWords318 CyclicQuotientEvaluation318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  [IsLocalRing S] [Nontrivial S]
variable (a : Action R A ι S)

/-- Every cyclic action over a nonzero local coefficient ring has a
literal original-element word tuple with unit determinant. This is local
chart completeness, not yet a global coefficient-localization cover. -/
lemma exists_word_chart
    (h : Function.Surjective (evaluation (linearAction R A ι S a) a.marked)) :
    ∃ w : ι → List A, IsUnit (determinant (point R A ι S a).val w) := by
  classical
  obtain ⟨κ,g,b,hb⟩ := Module.exists_basis_of_span_of_flat
    (generator R A ι S a) (span_eq_top R A ι S a h)
  let e : κ ≃ ι := b.indexEquiv (standardBasis ι S)
  let b' : Basis ι S (ι → S) := b.reindex e
  let w : ι → List A := fun j => [g (e.symm j)]
  refine ⟨w,?_⟩
  have hc : columns (point R A ι S a).val w=(standardBasis ι S).toMatrix b' := by
    ext i j
    rw [Basis.toMatrix_apply,← Basis.equivFun_apply]
    simp only [standardBasis,Basis.equivFun_ofEquivFun,LinearEquiv.refl_apply]
    change wordVector (point R A ι S a).val [g (e.symm j)] i=(b.reindex e) j i
    rw [Basis.reindex_apply,hb]
    simp [wordVector,point,generator]
  change IsUnit (columns (point R A ι S a).val w).det
  rw [hc]
  letI := Basis.invertibleToMatrix (standardBasis ι S) b'
  exact Matrix.isUnit_det_of_invertible _
end VaryingSourceLocalWordCover318
