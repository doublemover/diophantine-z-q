module
public import ActualTwoDescentRationalSupport318
public section
noncomputable section
namespace ActualTwoDescentAdjoinThreeSupport318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentRationalSquarefree318 ActualTwoDescentRationalSupport318
open ActualTwoDescentRationalPointPlaces318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def withThree (p : ι → ℕ) : Option ι → ℕ
  | none => 3
  | some i => p i

lemma withThree_injective (p : ι → ℕ) (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3) :
    Function.Injective (withThree p) := by
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (hp3 j he.symm)
  | some i =>
    cases j with
    | none => exact False.elim (hp3 i he)
    | some j => exact congrArg some (hd he)

lemma withThree_monomial (p : ι → ℕ) (b : Option ι → ZMod 2) :
    monomial (withThree p) b=firstRepresentative p (b none) (fun i => b (some i)) := by
  simp only [monomial,Fintype.prod_option,withThree,firstRepresentative]

/-- The first coordinate of an arbitrary actual rational point has exactly
the required positive3^delta times support-monomial representative. -/
theorem actual_rational_first_normalization (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (P : RationalPoint (∏ i, p i)) :
    ∃ (δ : ZMod 2) (u : ι → ZMod 2), ∃ r : ℚ, r ≠ 0 ∧
      P.x+3*(∏ i, p i : ℕ)=(firstRepresentative p δ u : ℚ)*r^2 := by
  letI : ∀ i, Fact (withThree p i).Prime := fun i => by
    cases i with
    | none => exact ⟨by decide⟩
    | some i => exact inferInstanceAs (Fact (p i).Prime)
  have hnpos : 0<∏ i, p i := Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have H : ∀ q : ℕ, q.Prime → (∀ i, q ≠ withThree p i) →
      Even (padicValRat q (P.x+3*(∏ i, p i : ℕ))) := by
    intro q hq hout
    exact actual_rational_first_support p hn P q hq (hout none) (fun i => hout (some i))
  obtain ⟨b,r,hr,he⟩ := actual_positive_supported_rational (withThree p)
    (withThree_injective p hd hp3) _ (actual_rational_first_positive _ hnpos P) H
  exact ⟨b none,(fun i => b (some i)),r,hr,by rwa [withThree_monomial] at he⟩

end ActualTwoDescentAdjoinThreeSupport318
