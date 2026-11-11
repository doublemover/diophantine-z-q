module
public import PolynomialValueResultant318
public import MonicComplexRootEnumeration318
public import LocalizedPolynomialEvaluationSeparation318
public section
noncomputable section
namespace LocalizedValueResultant318
open Polynomial ComplexPolynomialOpenPoints318
variable {ι : Type*}
variable (d : MvPolynomial ι ℂ) (Q H : Polynomial (Localization.Away d))

/-- The literal norm equation of H(beta) over the SAME base localization. -/
@[expose] def normPolynomial : Polynomial (Localization.Away d) :=
  PolynomialValueResultant318.equation Q H Q.natDegree (H.natDegree+1)

/-- At every actual base point its roots are precisely ALL H-values on
the full Q-root multiset, with multiplicity. Specialization and the
resultant construction retain fixed matrix sizes throughout. -/
theorem specialized_product (hm : Q.Monic) (v : ι → ℂ)
    (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ r : Fin Q.natDegree → ℂ,
      (∀ i, (Q.map (evaluation d v hv)).IsRoot (r i)) ∧
      (normPolynomial d Q H).map (evaluation d v hv) =
        ∏ i : Fin Q.natDegree, (X-C (H.eval₂ (evaluation d v hv) (r i))) := by
  let ev := evaluation d v hv
  obtain ⟨r,hQ,hr⟩ := MonicComplexRootEnumeration318.exists_roots
    (Q.map ev) (hm.map ev) Q.natDegree (hm.natDegree_map ev)
  refine ⟨r,hr,?_⟩
  rw [normPolynomial,PolynomialValueResultant318.equation_map]
  have hn : (PolynomialValueResultant318.relation (H.map ev)).natDegree ≤ H.natDegree+1 :=
    (PolynomialValueResultant318.relation_degree (H.map ev)).trans
      (Nat.add_le_add_right Polynomial.natDegree_map_le 1)
  simpa only [Polynomial.eval_map] using
    PolynomialValueResultant318.equation_product (Q.map ev) (H.map ev)
      Q.natDegree (H.natDegree+1) r hQ hn

/-- Monicity is proved in the whole localization by the actual full
fiber products and evaluation separation, not assumed from an abstract
norm or inferred from one generic point. -/
theorem monic (hd : d ≠ 0) (hm : Q.Monic) : (normPolynomial d Q H).Monic := by
  have hspecial (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
      ((normPolynomial d Q H).map (evaluation d v hv)).Monic ∧
      ((normPolynomial d Q H).map (evaluation d v hv)).natDegree=Q.natDegree := by
    obtain ⟨r,hr,hP⟩ := specialized_product d Q H hm v hv
    rw [hP]
    constructor
    · exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
    · rw [Polynomial.natDegree_prod_of_monic (fun _ _ => Polynomial.monic_X_sub_C _)]
      simp
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one Q.natDegree
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    apply LocalizedPolynomialEvaluationSeparation318.eq_zero d hd
    intro v hv
    have hh := Polynomial.coeff_eq_zero_of_natDegree_lt
      ((hspecial v hv).2.trans_lt hk)
    simpa only [Polynomial.coeff_map] using hh
  · apply LocalizedPolynomialEvaluationSeparation318.ext d hd
    intro v hv
    have hh := (hspecial v hv).1.coeff_natDegree
    rw [(hspecial v hv).2,Polynomial.coeff_map] at hh
    simpa only [map_one] using hh

/-- The same literal equation annihilates the specified polynomial value
in every target ring, with its original coefficient map. -/
theorem annihilates {A : Type*} [CommRing A]
    (φ : Localization.Away d →+* A) (β : A) (hβ : Q.eval₂ φ β=0) :
    (normPolynomial d Q H).eval₂ φ (H.eval₂ φ β)=0 :=
  PolynomialValueResultant318.annihilates Q H φ β hβ
end LocalizedValueResultant318
