module
public import LocalizedPrimitiveSelectedPolynomial318
public import WeightedRootProductBound318
public import WeightedMonicRootBound318
public section
noncomputable section
namespace LocalizedSelectedCoefficientBound318
open Polynomial
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

lemma selected_card_le (hm : Q.Monic) (hs : Q.Separable) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (selectedRoots d Q hm S v hv).card ≤ Q.natDegree := by
  classical
  have hcard : (allRoots d Q hm v hv).card = Q.natDegree := by
    let V := ComplexPolynomialOpenPoints318.evaluation d v hv
    letI : Fintype (Roots Q V) := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
      (rootsEquivRootSet Q V hm).symm
    change Fintype.card (Roots Q V) = Q.natDegree
    rw [Fintype.card_congr (rootsEquivRootSet Q V hm),
      Polynomial.card_rootSet_eq_natDegree hs.map (IsAlgClosed.splits _)]
    exact hm.natDegree_map V
  exact (Finset.card_filter_le _ _).trans_eq hcard

/-- The canonical selected coefficients inherit a bound from the
original entire monic candidate equation, with one fixed exponent equal
to its full degree. No constant selected degree or connectedness needed. -/
theorem selected_coefficient_bound (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
    (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hc : ∀ k < Q.natDegree, δ *
      ‖LocalizedComplexCoefficientAnalytic318.value d (Q.coeff k) v‖ ≤ A) (n : ℕ) :
    δ ^ Q.natDegree * ‖(selectedPolynomial d Q hm S v).coeff n‖ ≤
      (A+3*δ)^Q.natDegree := by
  classical
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  have hm' : (Q.map V).Monic := hm.map V
  have hc' : ∀ k < (Q.map V).natDegree, δ * ‖(Q.map V).coeff k‖ ≤ A := by
    intro k hk
    rw [hm.natDegree_map V] at hk
    simpa only [Polynomial.coeff_map,
      LocalizedComplexCoefficientAnalytic318.value_on_open d _ v hv] using hc k hk
  have hr (r : Roots Q V) : δ + δ*‖r.val‖ ≤ A+2*δ := by
    have hh := WeightedMonicRootBound318.root_bound (Q.map V) hm' δ A hδ hA hc' r.val r.property
    linarith
  have hh := WeightedRootProductBound318.coeff_bound_of_card_le
    (selectedRoots d Q hm S v hv) (fun r => r.val) δ (A+2*δ) hδ.le (by positivity)
    (fun r _ => hr r) Q.natDegree (selected_card_le d Q hm hs S v hv) n
  rw [selectedPolynomial_on_open d Q hm S v hv]
  change δ ^ Q.natDegree *
    ‖(∏ r ∈ selectedRoots d Q hm S v hv, (X-C r.val)).coeff n‖ ≤ _
  convert hh using 1 <;> congr 1 <;> ring
end LocalizedSelectedCoefficientBound318
