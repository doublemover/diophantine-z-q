module
public import ActualTwoDescentAdelicEightClasses318
public section
noncomputable section
namespace ActualTwoDescentActualAllPlacesBound318
set_option maxHeartbeats 16000000

open ActualTwoDescentAdelicPairData318 ActualTwoDescentAdelicEightClasses318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentEightClassCube318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentPrimeMonomials318
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma actual_squareclass_representative (z : SquareClass ℚ) : ∃ a : ℚ, ∃ ha : a ≠ 0, classOf a ha=z := by
  refine QuotientGroup.induction_on z ?_
  intro u
  refine ⟨(u : ℚ),u.ne_zero,?_⟩
  have he : Units.mk0 (u : ℚ) u.ne_zero=u := by ext; rfl
  rw [classOf,he]

/-- Every actual all-place class lies in the exact eight-element candidate cube. -/
theorem actual_all_places_cube_bound (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hn : (∏ i, p i) ≠ 0) (hb : monomial p beta ≠ 0)
    (z : allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)) :
    ∃ v : Cube, z.val=cubeClass ((∏ i, p i : ℕ) : ℚ) (monomial p beta : ℚ)
      (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hb) v := by
  obtain ⟨A,hA,heA⟩ := actual_squareclass_representative z.val.1
  obtain ⟨B,hB,heB⟩ := actual_squareclass_representative z.val.2
  have hez : z.val=(classOf A hA,classOf B hB) := Prod.ext heA.symm heB.symm
  have H : AdelicPair (∏ i, p i) A B := actual_adelic_pair_of_all_places _ hn A B hA hB (by
    rw [←hez]; exact z.property)
  obtain ⟨ε,c,e,r,s,hr,hs,hR,hS⟩ := actual_adelic_eight_classes p hd hp2 hp3 a beta N C A B H
  refine ⟨(ε,c,e),?_⟩
  rw [hez,actual_cube_literal]
  apply Prod.ext
  · exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,hR⟩
  · exact (class_of_eq_iff _ _ _ _).mpr ⟨s,hs,hS⟩

/-- Actual all-place membership is finite of cardinality at most eight.
This counts the intersection itself, not only its rational-image subgroup. -/
theorem actual_all_places_finite_bound (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hn : (∏ i, p i) ≠ 0) :
    Finite (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)) ∧
      Nat.card (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)) ≤ 8 := by
  have hb : monomial p beta ≠ 0 := (monomial_pos p beta).ne'
  let f : allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn) → Cube := fun z =>
    Classical.choose (actual_all_places_cube_bound p hd hp2 hp3 a beta N C hn hb z)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact (Classical.choose_spec (actual_all_places_cube_bound p hd hp2 hp3 a beta N C hn hb x)).trans
      ((congrArg (cubeClass ((∏ i, p i : ℕ) : ℚ) (monomial p beta : ℚ)
        (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hb)) he).trans
        (Classical.choose_spec (actual_all_places_cube_bound p hd hp2 hp3 a beta N C hn hb y)).symm)
  refine ⟨Finite.of_injective f hf,?_⟩
  simpa only [cube_card] using Nat.card_le_card_of_injective f hf

end ActualTwoDescentActualAllPlacesBound318
