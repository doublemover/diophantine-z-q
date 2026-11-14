module
public import CubicHomogeneousMarker318
public section
noncomputable section
namespace HomogeneousEvaluationScaling318
variable {σ K:Type*}[CommRing K]
lemma monomial_scale(k:σ→₀ℕ)(a:K)(v:σ→K):
    k.prod(fun i e=>(a*v i)^e)=a^k.degree*k.prod(fun i e=>v i^e):=by
  classical
  have hs:∀s:Finset σ,(∏i∈s,a^(k i))=a^(∑i∈s,k i):=by
    intro s
    induction s using Finset.induction_on with
    | empty=>simp only [Finset.prod_empty,Finset.sum_empty,pow_zero]
    | @insert i s hi ih=>rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,pow_add]
  simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,hs,Finsupp.degree_apply]
/-- Genuine homogeneous polynomial evaluation changes by exactly the
n-th power of a common scalar, including zero coordinates and scalar. -/
theorem evaluate_scale(p:MvPolynomial σ K)(n:ℕ)(hp:p.IsHomogeneous n)(a:K)(v:σ→K):
    MvPolynomial.eval (fun i=>a*v i) p=a^n*MvPolynomial.eval v p:=by
  classical
  have he(w:σ→K):MvPolynomial.eval w p=∑k∈p.support,
      p.coeff k*k.prod(fun i e=>w i^e):=by
    conv_lhs=>rw [←p.support_sum_monomial_coeff]
    simp only [map_sum,MvPolynomial.eval_monomial]
  rw [he,he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hn:n=k.degree:=by
    simpa only [Finsupp.degree_apply] using hp.degree_eq_sum_deg_support hk
  rw [monomial_scale,←hn]
  ring
end HomogeneousEvaluationScaling318
