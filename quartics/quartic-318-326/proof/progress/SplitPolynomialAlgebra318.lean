module
public import MonicEtaleSplitting318
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Algebra.Pi
public section
noncomputable section
namespace SplitPolynomialAlgebra318
open Polynomial
open scoped Function
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] {n:ℕ} (p:R[X]) (r:Fin n→R)
  (h:p=∏i,(X-C (r i)))

include h in
theorem root_eval (i:Fin n) : p.eval (r i)=0 := by
  rw [h,eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

include h in
theorem factors_coprime (hs:p.Separable) :
    Pairwise (IsCoprime on (fun i=>X-C (r i))) := by
  classical
  intro i j hij
  have hh:=hs
  rw [h,←Finset.insert_erase (Finset.mem_univ i),
    Finset.prod_insert (Finset.notMem_erase i Finset.univ),
    ←Finset.insert_erase (Finset.mem_erase_of_ne_of_mem (Ne.symm hij) (Finset.mem_univ j)),
    Finset.prod_insert (Finset.notMem_erase j (Finset.univ.erase i)),←mul_assoc] at hh
  exact hh.of_mul_left.isCoprime

@[expose] def evalHom : AdjoinRoot p→ₐ[R](Fin n→R) :=
  AlgHom.pi (fun i=>AdjoinRoot.liftAlgHom p (AlgHom.id R R) (r i)
    (by simpa using root_eval p r h i))

theorem evalHom_mk (f:R[X]) (i:Fin n) : evalHom p r h (AdjoinRoot.mk p f) i=f.eval (r i) := by
  simp [evalHom,AdjoinRoot.liftAlgHom_mk,Polynomial.aeval_def]

theorem evalHom_injective (hs:p.Separable) : Function.Injective (evalHom p r h) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective x
  apply AdjoinRoot.mk_eq_zero.mpr
  rw [h]
  apply Fintype.prod_dvd_of_coprime (factors_coprime p r h hs)
  intro i
  apply Polynomial.dvd_iff_isRoot.mpr
  have hh:=congrFun hx i
  simpa only [evalHom_mk,Pi.zero_apply,Polynomial.IsRoot.def] using hh

theorem evalHom_surjective (hs:p.Separable) : Function.Surjective (evalHom p r h) := by
  intro y
  let I:Fin n→Ideal R[X]:=fun i=>Ideal.span {X-C (r i)}
  have hI:Pairwise (IsCoprime on I):=by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (factors_coprime p r h hs hij)
  obtain ⟨f,hf⟩:=Ideal.pi_quotient_surjective hI
    (fun i=>Ideal.Quotient.mk (I i) (C (y i)))
  refine ⟨AdjoinRoot.mk p f,funext fun i=>?_⟩
  rw [evalHom_mk]
  have hh:=congrArg (Polynomial.quotientSpanXSubCAlgEquiv (r i)) (hf i)
  change (Polynomial.quotientSpanXSubCAlgEquiv (r i))
    (Ideal.Quotient.mk (Ideal.span {X-C (r i)}) f)=
    (Polynomial.quotientSpanXSubCAlgEquiv (r i))
    (Ideal.Quotient.mk (Ideal.span {X-C (r i)}) (C (y i))) at hh
  simpa only [Polynomial.quotientSpanXSubCAlgEquiv_mk,eval_C] using hh

@[expose] def evalEquiv (hs:p.Separable) : AdjoinRoot p≃ₐ[R](Fin n→R) :=
  AlgEquiv.ofBijective (evalHom p r h) ⟨evalHom_injective p r h hs,evalHom_surjective p r h hs⟩

theorem evalEquiv_mk (hs:p.Separable) (f:R[X]) (i:Fin n) :
    evalEquiv p r h hs (AdjoinRoot.mk p f) i=f.eval (r i) :=
  evalHom_mk p r h f i

end SplitPolynomialAlgebra318
