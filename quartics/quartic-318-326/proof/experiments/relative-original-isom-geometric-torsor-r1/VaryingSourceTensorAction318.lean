module
public import VaryingSourceActionClassifier318
public import OriginalWordBasisCyclicity318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
open scoped Matrix
namespace VaryingSourceTensorAction318
open VaryingSourceActionClassifier318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Action R A ι S)

/-- Actual scalar extension of the SAME original-source homomorphism.
The algebra is S tensor A, not a polynomial proxy for the source. -/
@[expose] def matrixAction : S ⊗[R] A →ₐ[S] Matrix ι ι S :=
  (AlgHom.liftEquiv R S A (Matrix ι ι S)) a.map
@[expose] def linearAction : S ⊗[R] A →ₐ[S] Module.End S (ι → S) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp (matrixAction R A ι S a)

lemma matrixAction_tmul (s : S) (x : A) :
    matrixAction R A ι S a (s ⊗ₜ[R] x)=s • a.map x :=
  AlgHom.liftEquiv_tmul a.map s x

lemma linearAction_tmul (s : S) (x : A) (v : ι → S) :
    linearAction R A ι S a (s ⊗ₜ[R] x) v=(s • a.map x) *ᵥ v := by
  change Matrix.toLinAlgEquiv' (matrixAction R A ι S a (s ⊗ₜ[R] x)) v=_
  rw [matrixAction_tmul,Matrix.toLinAlgEquiv'_apply]

/-- The literal selected source word acts by the very same matrices
used to define its determinant in the represented parameter. -/
lemma word_evaluation (l : List A) :
    CyclicQuotientEvaluation318.evaluation (linearAction R A ι S a) a.marked
      ((1 : S) ⊗ₜ[R] l.prod)=
      VaryingMatrixWords318.wordVector (point R A ι S a).val l := by
  change linearAction R A ι S a ((1 : S) ⊗ₜ[R] l.prod) a.marked=_
  rw [linearAction_tmul,one_smul]
  induction l with
  | nil => simp [VaryingMatrixWords318.wordVector,point]
  | cons x l ih =>
    simp only [List.prod_cons,map_mul,VaryingMatrixWords318.wordVector,point]
    rw [← Matrix.mulVec_mulVec,ih]
    rfl
end VaryingSourceTensorAction318
