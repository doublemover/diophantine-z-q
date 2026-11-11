module
public import LocalizedSelectedPolynomialAlgebraization318
public import LocalizedSelectedComplementProduct318
public import Mathlib.Algebra.Polynomial.FieldDivision
public section
noncomputable section
namespace IrreducibleLocalizedSelectedFactor318
open Polynomial Set ComplexPolynomialOpenPoints318
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318

/-- A factor that becomes a unit over an injective coefficient field has
degree zero already. Every monic specialization of that SAME factor is
therefore one, even when its coefficient maps may have nontrivial kernels. -/
lemma specialization_eq_one_of_field_unit {A K : Type*} [CommRing A] [Field K]
    (u : A →+* K) (hu : Function.Injective u) (P : Polynomial A)
    (hP : IsUnit (P.map u)) (v : A →+* ℂ) (hm : (P.map v).Monic) : P.map v = 1 := by
  have hn : (P.map u).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr
      (Polynomial.degree_eq_zero_of_isUnit hP).le
  rw [Polynomial.natDegree_map_eq_of_injective hu] at hn
  apply hm.natDegree_eq_zero.mp
  exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_map_le.trans_eq hn)

/-- A genuine nonempty clopen subset of the WHOLE simple-root locus
exhausts it when its actual defining equation remains irreducible over
an injective coefficient field. Both selected and complementary factors
are constructed from analytic coefficients, with actual growth and
polynomial numerators, before irreducibility is used. -/
theorem all_selected (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (ho : IsOpen S) (hc : IsClosed S) (hne : S.Nonempty)
    {K : Type*} [Field K] (u : Localization.Away d →+* K) (hu : Function.Injective u)
    (hirr : Irreducible (Q.map u)) : ∀ q : OpenRoots d Q, q ∈ S := by
  obtain ⟨H,hHd,hH⟩ := LocalizedSelectedPolynomialAlgebraization318.exists_selected_polynomial
    d hd Q hm hs S ho hc
  obtain ⟨G,hGd,hG⟩ := LocalizedSelectedPolynomialAlgebraization318.exists_selected_polynomial
    d hd Q hm hs Sᶜ hc.isOpen_compl ho.isClosed_compl
  have hprod : H*G = Q := by
    apply LocalizedPolynomialEvaluationSeparation318.polynomial_ext d hd
    intro v hv
    rw [Polynomial.map_mul,hH v hv,hG v hv]
    exact LocalizedSelectedComplementProduct318.selected_mul_complement d Q hm hs S v hv
  have hfield : Q.map u = H.map u * G.map u := by
    rw [←Polynomial.map_mul,hprod]
  rcases hirr.2 hfield with hHu | hGu
  · obtain ⟨q,hq⟩ := hne
    have hmH : (H.map (evaluation d q.val.val.1 q.property)).Monic := by
      rw [hH]
      exact selected_monic d Q hm S _ q.property
    have h1 := specialization_eq_one_of_field_unit u hu H hHu
      (evaluation d q.val.val.1 q.property) hmH
    rw [hH] at h1
    have hz := (selected_root_iff d Q hm S q).mpr hq
    rw [h1,Polynomial.eval_one] at hz
    exact (one_ne_zero hz).elim
  · intro q
    have hmG : (G.map (evaluation d q.val.val.1 q.property)).Monic := by
      rw [hG]
      exact selected_monic d Q hm Sᶜ _ q.property
    have h1 := specialization_eq_one_of_field_unit u hu G hGu
      (evaluation d q.val.val.1 q.property) hmG
    rw [hG] at h1
    exact LocalizedSelectedComplementProduct318.selected_of_complement_eq_one d Q hm S q h1
end IrreducibleLocalizedSelectedFactor318
