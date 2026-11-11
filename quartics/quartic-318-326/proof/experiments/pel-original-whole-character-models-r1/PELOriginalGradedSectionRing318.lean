module
public import PELOriginalSectionMultiplication318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace PELOriginalGradedSectionRing318
open Polynomial PELOriginalSectionMultiplication318
open PELOriginalPolarizationTransitions318
variable (τ:ℂ)(hτ:0<τ.im)
/-- The genuine original graded section algebra, faithfully represented
by finite formal sums of actual original section values. Degree n is
checked by the original local-holomorphy H0 predicate. No finite-generation
or projective algebraization assumption is part of this definition. -/
@[expose] def sectionAlgebra:Subalgebra ℂ (Polynomial (Values τ)) where
  carrier:={p|∀n,p.coeff n∈homogeneous τ hτ n}
  zero_mem':=by intro n;simp only [coeff_zero];exact (homogeneous τ hτ n).zero_mem
  one_mem':=by
    intro n
    by_cases hn:n=0
    · subst n
      simpa only [coeff_one_zero] using constant_mem τ hτ 1
    · simpa only [coeff_one,if_neg hn] using (homogeneous τ hτ n).zero_mem
  add_mem':=by
    intro p q hp hq n
    rw [coeff_add]
    exact (homogeneous τ hτ n).add_mem (hp n) (hq n)
  mul_mem':=by
    intro p q hp hq n
    rw [coeff_mul]
    apply (homogeneous τ hτ n).sum_mem
    intro ij hij
    have he:ij.1+ij.2=n:=Finset.mem_antidiagonal.mp hij
    have hm:=product_mem τ hτ ij.1 ij.2 (p.coeff ij.1) (q.coeff ij.2) (hp ij.1) (hq ij.2)
    rwa [he] at hm
  algebraMap_mem':=by
    intro c n
    change (Polynomial.C (fun _:Base τ=>c)).coeff n∈homogeneous τ hτ n
    by_cases hn:n=0
    · subst n
      simpa only [coeff_C_zero] using constant_mem τ hτ c
    · simpa only [coeff_C,if_neg hn] using (homogeneous τ hτ n).zero_mem
abbrev Ring:=sectionAlgebra τ hτ

/-- The actual degree-n section embeds as its single homogeneous term. -/
@[expose] def includeDegree(n:ℕ):homogeneous τ hτ n→ₗ[ℂ]Ring τ hτ where
  toFun s:=⟨Polynomial.monomial n s.val,by
    intro k
    by_cases hk:n=k
    · subst k
      simpa only [coeff_monomial,if_pos rfl] using s.property
    · simpa only [coeff_monomial,if_neg hk] using (homogeneous τ hτ k).zero_mem⟩
  map_add' s t:=by apply Subtype.ext;exact (Polynomial.monomial n).map_add _ _
  map_smul' c s:=by
    apply Subtype.ext
    simp only [Submodule.coe_smul,←Polynomial.smul_monomial]
lemma include_coefficient(n:ℕ)(s:homogeneous τ hτ n):
    (includeDegree τ hτ n s).val.coeff n=s.val:=by
  simp only [includeDegree,LinearMap.coe_mk,AddHom.coe_mk,coeff_monomial,if_pos rfl]
lemma include_injective(n:ℕ):Function.Injective (includeDegree τ hτ n):=by
  intro s t h
  apply Subtype.ext
  have he:=congrArg (fun p:Ring τ hτ=>p.val.coeff n) h
  simpa only [include_coefficient] using he

/-- Algebra multiplication restricts to the independently constructed
actual original power-line section multiplication, not a transported
basis-dependent product. -/
theorem homogeneous_product(m n:ℕ)(s:homogeneous τ hτ m)(t:homogeneous τ hτ n):
    includeDegree τ hτ m s*includeDegree τ hτ n t=
      includeDegree τ hτ (m+n) (multiply τ hτ m n s t):=by
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

/-- Every actual element is exactly its FINITE collection of original
homogeneous sections. Thus the polynomial realization adds no functions
or infinite sums to the graded H0 algebra. -/
theorem finite_homogeneous_decomposition(p:Ring τ hτ):
    p=∑n∈p.val.support,includeDegree τ hτ n ⟨p.val.coeff n,p.property n⟩:=by
  apply Subtype.ext
  change p.val=∑n∈p.val.support,Polynomial.monomial n (p.val.coeff n)
  simpa only [Polynomial.sum_def] using (Polynomial.sum_monomial_eq p.val).symm
end PELOriginalGradedSectionRing318
