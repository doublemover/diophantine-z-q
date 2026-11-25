module
public import OriginalSameJExactTruncatedMark318
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section
noncomputable section

open Algebra Polynomial
open scoped TensorProduct

namespace OriginalSameJAllOrderGraphBaseChange318
open OriginalSameJAllOrderGraphQuotient318 (testRing parameterPower thick graph graph_reads)
open OriginalSameJExactTruncatedMark318 (evalAt)

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

abbrev polynomials : (A⊗[k]k[X]) ≃ₐ[A] A[X] := (polyEquivTensor' k A).symm

def included : k[X] →+* (A⊗[k]k[X]) :=
  (Algebra.TensorProduct.includeRight : k[X] →ₐ[k] A⊗[k]k[X]).toRingHom

theorem parameter_map (m:ℕ) :
    parameterPower (A:=A) m = ((parameterPower (A:=k) m).map (included (A:=A))).map
      (polynomials (k:=k) (A:=A)).toRingHom := by
  unfold parameterPower thick
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton]
  have hX : (polynomials (k:=k) (A:=A)).toRingHom (included (A:=A) (X:k[X])) = (X:A[X]) := by
    change (polyEquivTensor k A).symm ((1:A)⊗ₜ[k](X:k[X])) = (X:A[X])
    rw [polyEquivTensor_symm_apply_tmul_eq_smul,Polynomial.map_X,one_smul]
  have hm : ((polynomials (k:=k) (A:=A)).toRingHom.comp (included (A:=A))) ((X:k[X])^m) =
      (X:A[X])^m :=
    (map_pow _ _ _).trans (congrArg (fun x : A[X] => x^m) hX)
  rw [hm]

/-- The actual affine base-change chart of X×Spec(k[t]/t^m), retaining
all nilpotents and the very same ordered parameter. -/
def productChart (m:ℕ) : A⊗[k]testRing (A:=k) m ≃ₐ[A] testRing (A:=A) m :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R:=k) A k[X] A (parameterPower m)).trans
    (Ideal.quotientEquivAlg _ _ polynomials (parameter_map (k:=k) (A:=A) m))

theorem tensor_reads (m:ℕ) (a:A) (p:k[X]) :
    productChart m (a⊗ₜ[k](Ideal.Quotient.mk (parameterPower m) p)) =
      Ideal.Quotient.mk (parameterPower m) (a • p.map (algebraMap k A)) := by
  rw [productChart,AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk]
  exact congrArg (Ideal.Quotient.mk (parameterPower (A:=A) m))
    (polyEquivTensor_symm_apply_tmul_eq_smul k A a p)

/-- On the real product chart the graph map is the scalar extension
of the retained truncated point, tested on every pure tensor. -/
theorem actual_graph_on_tensor (u : A) (m : ℕ) (a : A) (p : k[X]) :
    graph u m (productChart m (a⊗ₜ[k](Ideal.Quotient.mk (parameterPower m) p))) =
      Ideal.Quotient.mk (thick u m) a * Ideal.Quotient.mk (thick u m) (evalAt u p) := by
  rw [tensor_reads,graph_reads,Polynomial.smul_eq_C_mul,Polynomial.eval_mul,Polynomial.eval_C,
    map_mul]
  exact congrArg
    (fun b : A => Ideal.Quotient.mk (thick u m) a * Ideal.Quotient.mk (thick u m) b)
    (Polynomial.eval_map_algebraMap p u)

end OriginalSameJAllOrderGraphBaseChange318

#print axioms OriginalSameJAllOrderGraphBaseChange318.productChart
#print axioms OriginalSameJAllOrderGraphBaseChange318.tensor_reads
#print axioms OriginalSameJAllOrderGraphBaseChange318.actual_graph_on_tensor
