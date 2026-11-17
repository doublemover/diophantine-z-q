module
public import ActualTwoDescentArchimedeanRepresentation318
public section
noncomputable section
namespace ActualTwoDescentAllBadEquivalence318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentActualImageEquivalence318
open ActualTwoDescentArchimedeanRepresentation318 ActualTwoDescentFourTwoAdicClasses318
open ActualTwoDescentThreeUnitPoints318 ActualTwoDescentRepresentedSupport318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentLocalClassification318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Actual normalized local curve images at EVERY bad prime and infinity.
The support excludes2/3, and the literal cubic discriminant has no other
bad primes. Good-prime local sufficiency is still a separate obligation. -/
def AllBadRepresented (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  BadLocallyRepresented p δ u v ∧
  RepresentedAt 2 (∏ j, p j) (firstRepresentative p δ u) (monomial p v) ∧
  RealRepresented (∏ j, p j) (firstRepresentative p δ u) (monomial p v)

/-- Adding the actual2-adic and real places does not remove any of the
four surviving classes, proved by constructing their actual local points. -/
theorem actual_all_bad_equivalence (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hb : (monomial p beta : ZMod 8)=1)
    (δ : ZMod 2) (u v : Option U → ZMod 2) :
    AllBadRepresented p δ u v ↔ BadLocallyRepresented p δ u v := by
  constructor
  · exact fun H => H.1
  · intro H
    have hc := actual_represented_class_bound p hd hp2 hp3 a beta N C δ u v H
    obtain ⟨rfl,rfl,c,e,rfl⟩ := hc
    refine ⟨H,?_,?_⟩
    · have h2 := actual_four_two_adic_classes p beta hb c e
      simpa only [firstRepresentative,ZMod.val_zero,pow_zero,one_mul,
        monomial,Pi.zero_apply,Finset.prod_const_one] using actual_local_kummer_represented _ _ h2
    · simpa only [firstRepresentative,ZMod.val_zero,pow_zero,one_mul,
        monomial,Pi.zero_apply,Finset.prod_const_one] using
        actual_positive_real_representation (monomial p (c • ActualTwoDescentZeroSumCompletion318.ones _+e • beta))
          (∏ j, p j) (monomial_pos p _)

end ActualTwoDescentAllBadEquivalence318
