module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public section
noncomputable section
namespace HomogeneousSectionMarker318
open Polynomial
variable {σ A R:Type*}[CommRing A][CommRing R]
variable (d:ℕ)(f:A→+*R)(v:σ→R)
/-- Formal degree marker for actual whole-section homogeneous coordinates of arbitrary degree. -/
@[expose] def marker:MvPolynomial σ A→+*R[X]:=
  MvPolynomial.eval₂Hom (Polynomial.C.comp f) (fun i=>Polynomial.monomial d (v i))
lemma marked_product(k:σ→₀ℕ):
    k.prod (fun i e=>(Polynomial.monomial d (v i))^e)=
      Polynomial.monomial (d*k.degree) (k.prod (fun i e=>v i^e)):=by
  classical
  have hs:∀s:Finset σ,(∏i∈s,Polynomial.monomial (d*k i) (v i^k i))=
      Polynomial.monomial (d*∑i∈s,k i) (∏i∈s,v i^k i):=by
    intro s
    induction s using Finset.induction_on with
    | empty=>simp only [Finset.prod_empty,Finset.sum_empty,mul_zero,Polynomial.monomial_zero_one]
    | @insert i s hi ih=>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.prod_insert hi,ih,
        Polynomial.monomial_mul_monomial,Nat.mul_add]
  simpa only [Finsupp.prod,Finsupp.degree_apply,Polynomial.monomial_pow] using hs k.support
lemma marker_monomial(k:σ→₀ℕ)(a:A):
    marker d f v (MvPolynomial.monomial k a)=
      Polynomial.monomial (d*k.degree) (f a*k.prod (fun i e=>v i^e)):=by
  rw [marker,MvPolynomial.eval₂Hom_monomial,marked_product]
  change Polynomial.C (f a)*Polynomial.monomial (d*k.degree) _=_
  rw [←Polynomial.monomial_zero_left,Polynomial.monomial_mul_monomial,zero_add]
lemma marker_expansion(p:MvPolynomial σ A):
    marker d f v p=∑k∈p.support,Polynomial.monomial (d*k.degree)
      (f (p.coeff k)*k.prod (fun i e=>v i^e)):=by
  conv_lhs=>rw [←p.support_sum_monomial_coeff]
  simp only [map_sum,marker_monomial]
/-- For a genuinely homogeneous polynomial the original section marker
has exactly ONE degree, with its literal evaluation as coefficient. -/
lemma homogeneous_marker(p:MvPolynomial σ A)(n:ℕ)(hp:p.IsHomogeneous n):
    marker d f v p=Polynomial.monomial (d*n) (MvPolynomial.eval₂Hom f v p):=by
  classical
  have he:MvPolynomial.eval₂Hom f v p=∑k∈p.support,
      f (p.coeff k)*k.prod (fun i e=>v i^e):=by
    conv_lhs=>rw [←p.support_sum_monomial_coeff]
    simp only [map_sum,MvPolynomial.eval₂Hom_monomial]
  rw [marker_expansion,he,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hn:n=k.degree:=by
    simpa only [Finsupp.degree_apply] using hp.degree_eq_sum_deg_support hk
  rw [←hn]
end HomogeneousSectionMarker318
