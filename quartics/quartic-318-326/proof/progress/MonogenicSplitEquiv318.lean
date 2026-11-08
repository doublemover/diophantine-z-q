module
public import SplitPolynomialAlgebra318
public section
noncomputable section
namespace MonogenicSplitEquiv318
open Polynomial Algebra
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual monogenic algebra commutes with arbitrary scalar extension. -/
@[expose] def baseChange (p:R[X]) :
    S⊗[R]AdjoinRoot p≃ₐ[S]AdjoinRoot (p.map (algebraMap R S)) :=
  (AdjoinRoot.tensorAlgEquiv p
    (p.map (Algebra.TensorProduct.includeRight.toRingHom:R→+*S⊗[R]R)) rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) _ _ (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      congr 1
      ext a
      simp [Algebra.smul_def]))

theorem baseChange_root (p:R[X]) :
    baseChange (S:=S) p (1⊗ₜ[R]AdjoinRoot.root p)=
      AdjoinRoot.root (p.map (algebraMap R S)) := by
  simp [baseChange]

theorem baseChange_mk (p f:R[X]) :
    baseChange (S:=S) p (1⊗ₜ[R]AdjoinRoot.mk p f)=
      AdjoinRoot.mk (p.map (algebraMap R S)) (f.map (algebraMap R S)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,TensorProduct.tmul_add,hf,hg,Polynomial.map_add]
  | monomial n a =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,AdjoinRoot.mk_X,AdjoinRoot.mk_C,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
    change baseChange p (1⊗ₜ[R] (algebraMap R (AdjoinRoot p) a*(AdjoinRoot.root p)^n))=_
    have hm:(1:S)⊗ₜ[R](algebraMap R (AdjoinRoot p) a*(AdjoinRoot.root p)^n)=
        (1⊗ₜ[R]algebraMap R (AdjoinRoot p) a)*(1⊗ₜ[R]AdjoinRoot.root p)^n := by
      rw [Algebra.TensorProduct.tmul_pow,Algebra.TensorProduct.tmul_mul_tmul,one_pow,one_mul]
    rw [hm,map_mul,map_pow,baseChange_root]
    congr 1
    change baseChange p (1⊗ₜ[R]algebraMap R (AdjoinRoot p) a)=_
    rw [←Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact (baseChange (S:=S) p).commutes (algebraMap R S a)

variable {n:ℕ} (p:R[X]) (r:Fin n→S)
  (h:p.map (algebraMap R S)=∏i,(X-C (r i))) (hs:p.Separable)

/-- Evaluation gives the actual splitting of the original polynomial algebra,
not merely an equality of degrees or an unspecified product decomposition. -/
@[expose] def splitEquiv : S⊗[R]AdjoinRoot p≃ₐ[S](Fin n→S) :=
  (baseChange p).trans (SplitPolynomialAlgebra318.evalEquiv _ r h hs.map)

theorem splitEquiv_one_tmul_mk (f:R[X]) (i:Fin n) :
    splitEquiv p r h hs (1⊗ₜ[R]AdjoinRoot.mk p f) i=f.eval₂ (algebraMap R S) (r i) := by
  simp only [splitEquiv,AlgEquiv.trans_apply,baseChange_mk,
    SplitPolynomialAlgebra318.evalEquiv_mk,Polynomial.eval_map]

theorem splitEquiv_tmul_mk (s:S) (f:R[X]) (i:Fin n) :
    splitEquiv p r h hs (s⊗ₜ[R]AdjoinRoot.mk p f) i=s*f.eval₂ (algebraMap R S) (r i) := by
  have hh:s⊗ₜ[R]AdjoinRoot.mk p f=
      algebraMap S (S⊗[R]AdjoinRoot p) s*(1⊗ₜ[R]AdjoinRoot.mk p f) := by
    change s⊗ₜ[R]AdjoinRoot.mk p f=(s⊗ₜ[R]1)*(1⊗ₜ[R]AdjoinRoot.mk p f)
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  rw [hh,map_mul,AlgEquiv.commutes]
  change s*(splitEquiv p r h hs (1⊗ₜ[R]AdjoinRoot.mk p f) i)=_
  rw [splitEquiv_one_tmul_mk]

end MonogenicSplitEquiv318

namespace MonicEtaleSplitting318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 0
universe u
variable {R:Type u} [CommRing R] [Nontrivial R] (p:R[X]) (hp:p.Monic) (hs:p.Separable)

/-- A constructed finite-etale faithfully-flat algebra that splits the
original monic separable algebra by the actual evaluation map. -/
@[expose] def canonicalSplitEquiv :
    (splitting p hp hs).S⊗[R]AdjoinRoot p≃ₐ[(splitting p hp hs).S]
      (Fin p.natDegree→(splitting p hp hs).S) :=
  MonogenicSplitEquiv318.splitEquiv p (splitting p hp hs).roots
    (splitting p hp hs).factorization hs

end MonicEtaleSplitting318
