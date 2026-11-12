module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public section
noncomputable section
namespace QuadraticMonomialCoordinates318
variable (ι:Type*) [Fintype ι] [DecidableEq ι]
abbrev Index:=Sym ι 2
@[expose] def pair(r s:ι):Index ι:=⟨{r,s},by simp⟩
lemma exists_pair(a:Index ι):∃r s,a=pair ι r s:=by
  obtain ⟨r,t,ht⟩:=Sym.exists_eq_cons_of_succ a
  obtain ⟨s,z,hz⟩:=Sym.exists_eq_cons_of_succ t
  have hz0:=Sym.eq_nil_of_card_zero z
  refine ⟨r,s,?_⟩
  rw [ht,hz,hz0]
  rfl
@[expose] def first(a:Index ι):ι:=Classical.choose (exists_pair ι a)
@[expose] def second(a:Index ι):ι:=Classical.choose (Classical.choose_spec (exists_pair ι a))
lemma actual_pair(a:Index ι):a=pair ι (first ι a) (second ι a):=
  Classical.choose_spec (Classical.choose_spec (exists_pair ι a))
@[expose] def exponent(a:Index ι):ι→₀ℕ:=a.val.toFinsupp
lemma exponent_injective:Function.Injective (exponent ι):=by
  intro a b h
  apply Subtype.ext
  exact Multiset.toFinsupp.injective h
lemma exponent_degree(a:Index ι):(exponent ι a).degree=2:=by
  change a.val.toFinsupp.sum (fun _=>id)=2
  rw [Multiset.toFinsupp_sum_eq]
  exact a.property
lemma exponent_pair(r s:ι):
    exponent ι (pair ι r s)=Finsupp.single r 1+Finsupp.single s 1:=by
  change Multiset.toFinsupp ({r}+{s})=_
  rw [map_add,Multiset.toFinsupp_singleton,Multiset.toFinsupp_singleton]
lemma monomial_pair(r s:ι):
    MvPolynomial.monomial (exponent ι (pair ι r s)) (1:ℂ)=
      MvPolynomial.X r*MvPolynomial.X s:=by
  rw [exponent_pair]
  change MvPolynomial.monomial (Finsupp.single r 1+Finsupp.single s 1) 1=
    MvPolynomial.monomial (Finsupp.single r 1) 1*MvPolynomial.monomial (Finsupp.single s 1) 1
  rw [MvPolynomial.monomial_mul_monomial,one_mul]
/-- Independent coordinates on the distinct quadratic monomials. For
nine variables these are 45 monomials,
not 81 ordered products with spurious antisymmetric kernel relations. -/
@[expose] def polynomial:(Index ι→ℂ)→ₗ[ℂ]MvPolynomial ι ℂ where
  toFun c:=∑a:Index ι,MvPolynomial.monomial (exponent ι a) (c a)
  map_add' c d:=by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c d:=by simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]
lemma coefficient(c:Index ι→ℂ)(a:Index ι):
    MvPolynomial.coeff (exponent ι a) (polynomial ι c)=c a:=by
  classical
  simp [polynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,
    (exponent_injective ι).eq_iff]
lemma polynomial_injective:Function.Injective (polynomial ι):=by
  intro c d h
  funext a
  have he:=congrArg (MvPolynomial.coeff (exponent ι a)) h
  simpa only [coefficient] using he
lemma homogeneous(c:Index ι→ℂ):(polynomial ι c).IsHomogeneous 2:=by
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  exact MvPolynomial.isHomogeneous_monomial (c a) (exponent_degree ι a)
lemma polynomial_basis(a:Index ι):
    polynomial ι (Pi.single a 1)=MvPolynomial.monomial (exponent ι a) 1:=by
  simp [polynomial]
lemma monomial_actual_pair(a:Index ι):
    MvPolynomial.monomial (exponent ι a) (1:ℂ)=
      MvPolynomial.X (first ι a)*MvPolynomial.X (second ι a):=by
  conv_lhs=>rw [actual_pair ι a]
  exact monomial_pair ι _ _
lemma coefficient_off_degree(p:MvPolynomial ι ℂ)(hp:p.IsHomogeneous 2)
    (d:ι→₀ℕ)(hd:d.degree≠2):p.coeff d=0:=by
  by_contra hc
  have he:=hp.degree_eq_sum_deg_support (MvPolynomial.mem_support_iff.mpr hc)
  exact hd (by simpa only [Finsupp.degree_apply] using he.symm)
/-- Every genuine homogeneous quadratic has these unordered-monomial
coordinates. The matrix below therefore does not omit any quadratic
relations either. -/
theorem all_quadratics(p:MvPolynomial ι ℂ)(hp:p.IsHomogeneous 2):
    polynomial ι (fun a=>p.coeff (exponent ι a))=p:=by
  apply MvPolynomial.ext
  intro d
  by_cases hd:d.degree=2
  · let a:Index ι:=⟨d.toMultiset,by
      rw [Finsupp.card_toMultiset]
      exact hd⟩
    have ha:exponent ι a=d:=Multiset.toFinsupp_toMultiset d
    simpa only [ha] using coefficient ι (fun a=>p.coeff (exponent ι a)) a
  · rw [coefficient_off_degree ι _ (homogeneous ι _) d hd,
      coefficient_off_degree ι p hp d hd]
end QuadraticMonomialCoordinates318
