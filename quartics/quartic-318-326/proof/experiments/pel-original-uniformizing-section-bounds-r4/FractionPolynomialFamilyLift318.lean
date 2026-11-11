module
public import FractionFiniteCoefficientLift318
public import Mathlib.Algebra.Polynomial.Eval.Defs
public section
noncomputable section
namespace FractionPolynomialFamilyLift318
open Polynomial
open scoped BigOperators
variable (R K:Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
/-- One genuine original-ring denominator lifts ALL coefficients of a
finite family of polynomials. Each polynomial maps back exactly, not
merely up to a scalar or a relation in an unspecified field. -/
theorem exists_lift {ι:Type*} [Fintype ι](f:ι→Polynomial K):
    ∃d:R,∃hd:d≠0,∃g:ι→Polynomial (Localization.Away d),
      ∀i,Polynomial.map (FractionFiniteCoefficientLift318.toField R K d hd) (g i)=f i:=by
  classical
  let J:=Σi:ι,{n:ℕ // n∈(f i).support}
  obtain ⟨d,hd,c,hc⟩:=FractionFiniteCoefficientLift318.exists_lift R K
    (fun a:J=>(f a.1).coeff a.2)
  let g(i:ι):Polynomial (Localization.Away d):=
    ∑n∈(f i).support,monomial n (if h:n∈(f i).support then c ⟨i,⟨n,h⟩⟩ else 0)
  refine ⟨d,hd,g,?_⟩
  intro i
  change Polynomial.map _ (∑n∈(f i).support,
    monomial n (if h:n∈(f i).support then c ⟨i,⟨n,h⟩⟩ else 0))=f i
  rw [Polynomial.map_sum]
  calc
    _=∑n∈(f i).support,monomial n ((f i).coeff n):=by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Polynomial.map_monomial,dif_pos hn,hc]
    _=f i:=Polynomial.sum_monomial_eq (f i)
end FractionPolynomialFamilyLift318
