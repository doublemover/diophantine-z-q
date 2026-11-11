module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public section
noncomputable section
namespace CubicHomogeneousMarker318
open Polynomial
variable {σ A R:Type*}[CommRing A][CommRing R]
variable (f:A→+*R)(v:σ→R)
/-- Formal degree marker for actual cubic homogeneous coordinates. -/
@[expose] def marker:MvPolynomial σ A→+*R[X]:=
  MvPolynomial.eval₂Hom (Polynomial.C.comp f) (fun i=>Polynomial.monomial 3 (v i))
lemma marked_product(k:σ→₀ℕ):
    k.prod (fun i e=>(Polynomial.monomial 3 (v i))^e)=
      Polynomial.monomial (3*k.degree) (k.prod (fun i e=>v i^e)):=by
  classical
  have hs:∀s:Finset σ,(∏i∈s,Polynomial.monomial (3*k i) (v i^k i))=
      Polynomial.monomial (3*∑i∈s,k i) (∏i∈s,v i^k i):=by
    intro s
    induction s using Finset.induction_on with
    | empty=>simp only [Finset.prod_empty,Finset.sum_empty,mul_zero,Polynomial.monomial_zero_one]
    | @insert i s hi ih=>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.prod_insert hi,ih,
        Polynomial.monomial_mul_monomial,Nat.mul_add]
  simpa only [Finsupp.prod,Finsupp.degree_apply,Polynomial.monomial_pow] using hs k.support
lemma marker_monomial(k:σ→₀ℕ)(a:A):
    marker f v (MvPolynomial.monomial k a)=
      Polynomial.monomial (3*k.degree) (f a*k.prod (fun i e=>v i^e)):=by
  rw [marker,MvPolynomial.eval₂Hom_monomial,marked_product]
  change Polynomial.C (f a)*Polynomial.monomial (3*k.degree) _=_
  rw [←Polynomial.monomial_zero_left,Polynomial.monomial_mul_monomial,zero_add]
lemma marker_expansion(p:MvPolynomial σ A):
    marker f v p=∑k∈p.support,Polynomial.monomial (3*k.degree)
      (f (p.coeff k)*k.prod (fun i e=>v i^e)):=by
  conv_lhs=>rw [←p.support_sum_monomial_coeff]
  simp only [map_sum,marker_monomial]
lemma coefficient(p:MvPolynomial σ A)(n:ℕ):
    (marker f v p).coeff (3*n)=∑k∈p.support with k.degree=n,
      f (p.coeff k)*k.prod (fun i e=>v i^e):=by
  classical
  rw [marker_expansion,Polynomial.finsetSum_coeff,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have he:3*k.degree=3*n↔k.degree=n:=by omega
  simp only [Polynomial.coeff_monomial,he]

/-- The true homogeneous component is recovered by one actual formal
coefficient. Distinct polynomial degrees cannot cancel in this map. -/
theorem homogeneous_component(p:MvPolynomial σ A)(n:ℕ):
    marker f v (MvPolynomial.homogeneousComponent n p)=
      Polynomial.monomial (3*n) ((marker f v p).coeff (3*n)):=by
  classical
  rw [MvPolynomial.homogeneousComponent_apply,map_sum,coefficient,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hn:k.degree=n:=(Finset.mem_filter.mp hk).2
  rw [marker_monomial,hn]
/-- For a genuinely homogeneous polynomial the original section marker
has exactly ONE degree, with its literal evaluation as coefficient. -/
lemma homogeneous_marker(p:MvPolynomial σ A)(n:ℕ)(hp:p.IsHomogeneous n):
    marker f v p=Polynomial.monomial (3*n) (MvPolynomial.eval₂Hom f v p):=by
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
end CubicHomogeneousMarker318
