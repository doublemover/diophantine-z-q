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
  rw [Ideal.map_map]
  let f : k[X] →+* A[X] :=
    (polynomials (k:=k) (A:=A)).toRingHom.comp (included (A:=A))
  have hX : (polynomials (k:=k) (A:=A)).toRingHom (included (A:=A) (X:k[X])) = (X:A[X]) := by
    change (polyEquivTensor k A).symm ((1:A)⊗ₜ[k](X:k[X])) = (X:A[X])
    rw [polyEquivTensor_symm_apply_tmul_eq_smul,Polynomial.map_X,one_smul]
  have hm : f ((X:k[X])^m) = (X:A[X])^m :=
    (map_pow f (X:k[X]) m).trans (congrArg (fun x : A[X] => x^m) hX)
  have hi : (f : k[X] → A[X]) '' Set.singleton ((X:k[X])^m) =
      Set.singleton (f ((X:k[X])^m)) :=
    Set.image_singleton
  change Ideal.span (Set.singleton ((X:A[X])^m)) =
    Ideal.map f (Ideal.span (Set.singleton ((X:k[X])^m)))
  calc
    _ = Ideal.span (Set.singleton (f ((X:k[X])^m))) :=
      congrArg (fun x : A[X] => Ideal.span (Set.singleton x)) hm.symm
    _ = Ideal.span ((f : k[X] → A[X]) '' Set.singleton ((X:k[X])^m)) :=
      congrArg Ideal.span hi.symm
    _ = _ := (Ideal.map_span f (Set.singleton ((X:k[X])^m))).symm

/-- The actual affine base-change chart of X×Spec(k[t]/t^m), retaining
all nilpotents and the very same ordered parameter. -/
def productChart (m:ℕ) : A⊗[k]testRing (A:=k) m ≃ₐ[A] testRing (A:=A) m :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R:=k) A k[X] A (parameterPower m)).trans
    (Ideal.quotientEquivAlg _ _ polynomials (parameter_map (k:=k) (A:=A) m))

theorem tensor_reads (m:ℕ) (a:A) (p:k[X]) :
    productChart m (a⊗ₜ[k](Ideal.Quotient.mk (parameterPower m) p)) =
      Ideal.Quotient.mk (parameterPower m) (a • p.map (algebraMap k A)) := by
  rw [productChart,AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  let J : Ideal A[X] := parameterPower (A:=A) m
  let I : Ideal (A⊗[k]k[X]) := (parameterPower (A:=k) m).map (included (A:=A))
  let g : (A⊗[k]k[X]) ≃ₐ[A] A[X] := polynomials
  let h : J = I.map g.toRingHom := parameter_map (k:=k) (A:=A) m
  let z : A⊗[k]k[X] := a⊗ₜ[k]p
  change Ideal.quotientEquivAlg I J g h (Ideal.Quotient.mk I z) =
    Ideal.Quotient.mk J (a • p.map (algebraMap k A))
  calc
    _ = Ideal.Quotient.mk J (g z) := Ideal.quotientEquivAlg_mk J g h z
    _ = _ := congrArg (Ideal.Quotient.mk J)
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
