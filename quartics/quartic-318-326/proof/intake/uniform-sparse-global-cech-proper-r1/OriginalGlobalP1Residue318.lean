module
public import OriginalGlobalCechRemainder318
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace OriginalGlobalP1Residue318
open Polynomial
open scoped LaurentPolynomial
variable {E : Type*} [Field E]

@[expose] def mon (a:E) (n:ℤ) : LaurentPolynomial E := LaurentPolynomial.C a*LaurentPolynomial.T n
@[expose] def res (h:LaurentPolynomial E) : E := h.coeff (-1)
@[expose] def cu (p:E[X]) : LaurentPolynomial E := toLaurent p
/-- dv=-x⁻²dx is essential; both powers −1 and 0 would disappear with a
wrong identification of the cotangent transition. -/
@[expose] def cv (p:E[X]) : LaurentPolynomial E :=
  -(aeval (LaurentPolynomial.T (-1)) p*LaurentPolynomial.T (-2))

theorem res_mon (a:E) (n:ℤ) : res (mon a n) = if n= -1 then a else 0 := by
  rw [res,mon,←LaurentPolynomial.single_eq_C_mul_T]
  exact Finsupp.single_apply

@[simp] theorem res_add (h g:LaurentPolynomial E) : res (h+g)=res h+res g := rfl
@[simp] theorem res_neg (h:LaurentPolynomial E) : res (-h) = -res h := rfl
@[simp] theorem res_zero : res (0:LaurentPolynomial E)=0 := rfl
@[simp] theorem cu_add (p q:E[X]) : cu (p+q)=cu p+cu q := map_add toLaurent p q
@[simp] theorem cv_add (p q:E[X]) : cv (p+q)=cv p+cv q := by simp only [cv,map_add,add_mul,neg_add]
@[simp] theorem cu_zero : cu (0:E[X])=0 := map_zero toLaurent
@[simp] theorem cv_zero : cv (0:E[X])=0 := by simp [cv]
@[simp] theorem cu_mono (n:ℕ) (a:E) : cu (monomial n a)=mon a n := Polynomial.toLaurent_C_mul_T n a
@[simp] theorem cv_mono (n:ℕ) (a:E) : cv (monomial n a)=mon (-a) (-(n:ℤ)-2) := by
  rw [cv,← C_mul_X_pow_eq_monomial, map_mul,aeval_C,aeval_X_pow,LaurentPolynomial.T_pow,
    LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply,
    LaurentPolynomial.mul_T_assoc,mon,map_neg,neg_mul]
  congr 3
  omega

theorem chart_zero (p:E[X]) : res (cu p)=0 ∧ res (cv p)=0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a =>
    simp only [cu_mono,cv_mono,res_mon,ite_eq_right (show (n:ℤ) ≠ -1 by omega),
      ite_eq_right (show -(n:ℤ)-2 ≠ -1 by omega),and_self]

theorem normal_form (h:LaurentPolynomial E) :
    ∃ p q:E[X], h=cu p+cv q+mon (res h) (-1) := by
  induction h using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨p,q,hp⟩:=ha
    obtain ⟨u,v,hu⟩:=hb
    refine ⟨p+u,q+v,?_⟩
    rw [cu_add,cv_add,res_add]
    have H (a b:E) : mon (a+b) (-1)=mon a (-1)+mon b (-1) := by simp only [mon,map_add,add_mul]
    rw [H]
    linear_combination hp+hu
  | C_mul_T n a =>
    change ∃ p q:E[X], mon a n=cu p+cv q+mon (res (mon a n)) (-1)
    by_cases e : n= -1
    · subst n; refine ⟨0,0,?_⟩; simp [res_mon]
    · rw [res_mon,ite_eq_right e]
      have hz : mon (0:E) (-1)=0 := by simp [mon]
      rw [hz]
      by_cases hn : 0≤n
      · refine ⟨monomial n.toNat a,0,?_⟩
        simp [Int.toNat_of_nonneg hn]
      · refine ⟨0,monomial (-n-2).toNat (-a),?_⟩
        have hi : 0≤ -n-2 := by omega
        simp only [cu_zero,cv_mono,neg_neg,Int.toNat_of_nonneg hi,zero_add,add_zero]
        congr 1
        omega

/-- Exact presentation of the standard two-chart cohomology quotient:
p(x)dx and q(v)dv give all and only the zero-residue Laurent forms. -/
theorem exact_cech (h:LaurentPolynomial E) : res h=0 ↔ ∃ p q:E[X], h=cu p+cv q := by
  constructor
  · intro hz
    obtain ⟨p,q,hp⟩:=normal_form h
    exact ⟨p,q,by simpa [hz,mon] using hp⟩
  · rintro ⟨p,q,rfl⟩
    rw [res_add,(chart_zero p).1,(chart_zero q).2,add_zero]
end OriginalGlobalP1Residue318
#print axioms OriginalGlobalP1Residue318.exact_cech
