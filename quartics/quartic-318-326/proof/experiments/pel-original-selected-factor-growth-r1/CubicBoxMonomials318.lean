module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Fintype.Pi
public section
noncomputable section
namespace CubicBoxMonomials318
open scoped BigOperators
abbrev Box(m:ℕ):=Fin 3→Fin (m+1)
@[expose] def exponent {m:ℕ}(a:Box m):Fin 3→₀ℕ:=
  Finsupp.equivFunOnFinite.symm (fun i=>(a i).val)
@[simp] lemma exponent_apply {m:ℕ}(a:Box m)(i:Fin 3):exponent a i=(a i).val:=by
  simp [exponent]
lemma exponent_injective(m:ℕ):Function.Injective (exponent (m:=m)):=by
  intro a b h
  funext i
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun d:Fin 3→₀ℕ=>d i) h
@[expose] def total {m:ℕ}(a:Box m):ℕ:=∑i:Fin 3,(a i).val
lemma total_le {m:ℕ}(a:Box m):total a≤3*m:=by
  have h0:((a 0).val)≤m:=Nat.le_of_lt_succ (a 0).isLt
  have h1:((a 1).val)≤m:=Nat.le_of_lt_succ (a 1).isLt
  have h2:((a 2).val)≤m:=Nat.le_of_lt_succ (a 2).isLt
  simp only [total,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  omega
@[expose] def polynomial(m:ℕ):(Box m→ℂ)→ₗ[ℂ]MvPolynomial (Fin 3) ℂ where
  toFun c:=∑a:Box m,MvPolynomial.monomial (exponent a) (c a)
  map_add' c d:=by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c d:=by simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]
lemma coefficient(m:ℕ)(c:Box m→ℂ)(a:Box m):
    MvPolynomial.coeff (exponent a) (polynomial m c)=c a:=by
  classical
  simp [polynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,
    (exponent_injective m).eq_iff]
lemma polynomial_injective(m:ℕ):Function.Injective (polynomial m):=by
  intro c d h
  funext a
  simpa only [coefficient] using congrArg (MvPolynomial.coeff (exponent a)) h
lemma evaluation {K:Type*}[Field K][Algebra ℂ K](m:ℕ)(c:Box m→ℂ)(z:Fin 3→K):
    MvPolynomial.aeval z (polynomial m c)=
      ∑a:Box m,algebraMap ℂ K (c a)*∏i:Fin 3,z i^(a i).val:=by
  rw [polynomial,map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.aeval_monomial,Finsupp.prod_fintype]
  · simp only [exponent_apply]
  · intro i;exact pow_zero _
lemma card(m:ℕ):Fintype.card (Box m)=(m+1)^3:=by
  simp [Box,Fintype.card_fun]
end CubicBoxMonomials318
