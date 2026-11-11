module
public import LocalizedAnalyticPolynomialFamily318
public import LocalizedSelectedPolynomialGrowth318
public section
noncomputable section
namespace LocalizedSelectedPolynomialAlgebraization318
open Polynomial Set
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318

lemma degree_le (d : MvPolynomial (Fin 2) ℂ) (Q : Polynomial (Localization.Away d))
    (hm : Q.Monic) (hs : Q.Separable) (S : Set (OpenRoots d Q))
    (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (selectedPolynomial d Q hm S v).natDegree ≤ Q.natDegree := by
  rw [selectedPolynomial_on_open d Q hm S v hv]
  change (∏ r ∈ selectedRoots d Q hm S v hv, (X-C r.val)).natDegree ≤ _
  rw [Polynomial.natDegree_prod_of_monic (fun _ _ => Polynomial.monic_X_sub_C _)]
  simpa using LocalizedSelectedCoefficientBound318.selected_card_le d Q hm hs S v hv

/-- The canonical selected fiber product is now an ACTUAL polynomial
over the original base localization, uniformly on the whole base open.
Analyticity and growth are derived from the clopen subset and the given
monic separable equation; algebraicity is not an assumption. -/
theorem exists_selected_polynomial (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (ho : IsOpen S) (hc : IsClosed S) :
    ∃ H : Polynomial (Localization.Away d), H.natDegree ≤ Q.natDegree ∧
      ∀ v (hv : MvPolynomial.eval v d ≠ 0),
        H.map (ComplexPolynomialOpenPoints318.evaluation d v hv) = selectedPolynomial d Q hm S v := by
  obtain ⟨M,N,C,hC,hb⟩ := LocalizedSelectedPolynomialGrowth318.exists_selected_growth d Q hm hs S
  exact LocalizedAnalyticPolynomialFamily318.exists_polynomial d hd
    (selectedPolynomial d Q hm S) Q.natDegree M N C hC
    (degree_le d Q hm hs S)
    (fun n v hv => selected_coeff_analytic d Q hm hs S ho hc v hv n)
    (fun n v hv => hb v hv n)
end LocalizedSelectedPolynomialAlgebraization318
