module
public import ActualSourceHOneSmallPoles318
public import ContactPrincipalCoefficientExpansion318

public section
noncomputable section
namespace ActualSourceHOneFiveSpanning318
open RootOrderMonomialBasis318
open ActualSourceHOnePrincipalRepresentatives318 ActualSourceHOneSmallPoles318
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Each candidate is an additive rational-coefficient map to actual H1.
Scalars are applied in the original overlap ring before taking the boundary. -/
@[expose] def poleMap (k : ℕ) (i : ThreeIndex) : ℚ →+ HOne where
  toFun q := poleClass q k i
  map_zero' := by simp only [poleClass,map_zero,zero_mul]
  map_add' q r := by simp only [poleClass,map_add,add_mul]

/-- The sum of the five concrete rational-coefficient candidate maps. -/
@[expose] def fiveCoefficients : (SmallIndex → ℚ) →+ HOne where
  toFun q := ∑ s, poleMap s.val.2.val s.val.1 (q s)
  map_zero' := by simp only [Pi.zero_apply,map_zero,Finset.sum_const_zero]
  map_add' q r := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]

/-- Every individual small-pole class is in the range of the same five-map sum. -/
theorem small_pole_in_range (s : SmallIndex) (q : ℚ) :
    poleClass q s.val.2.val s.val.1 ∈ fiveCoefficients.range := by
  classical
  refine ⟨(fun t => if t = s then q else 0),?_⟩
  change (∑ t, poleMap t.val.2.val t.val.1 (if t = s then q else 0)) = _
  simp only [apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] <;> rfl

/-- Every weighted pole belongs to the five-map range: surviving poles have
a complete candidate index, and all other poles vanish by the actual charts. -/
theorem pole_in_range (q : ℚ) (k : ℕ) (i : ThreeIndex) :
    poleClass q k i ∈ fiveCoefficients.range := by
  by_cases hk : 0 < k ∧ k < ContactFinitePoleReduction318.weight i
  · let s : SmallIndex := ⟨(i,⟨k,small_pole_lt_three i k hk.2⟩),hk⟩
    exact small_pole_in_range s q
  · rw [poleClass_zero_outside_small q k i hk]
    exact fiveCoefficients.range.zero_mem

/-- Polynomial principal representatives expand using every nonzero coefficient. -/
theorem principalClass_expansion (P : Polynomial ℚ) (n : ℕ)
    (hP : P.degree < (n : WithBot ℕ)) (i : ThreeIndex) :
    principalClass P n i = ∑ j ∈ P.support, poleClass (P.coeff j) (n-j) i := by
  unfold principalClass
  rw [ContactPrincipalCoefficientExpansion318.principalTerm_expansion units P n hP,
    Finset.sum_mul,map_sum] <;> rfl

/-- Every bounded polynomial principal class is in the range of the actual
five coefficient maps. No unproved independence premise is used. -/
theorem principal_in_range (P : Polynomial ℚ) (n : ℕ)
    (hP : P.degree < (n : WithBot ℕ)) (i : ThreeIndex) :
    principalClass P n i ∈ fiveCoefficients.range := by
  rw [principalClass_expansion P n hP i]
  exact fiveCoefficients.range.sum_mem (fun j _ => pole_in_range (P.coeff j) (n-j) i)

/-- The original whole-source H1 is an additive quotient of five copies of Q,
through five explicit original overlap classes. This proves spanning only;
independence and identification with the quotient pullbacks are separate. -/
theorem fiveCoefficients_surjective : Function.Surjective fiveCoefficients := by
  intro y
  obtain ⟨n,R,hR,hy⟩ := principal_representatives y
  have hmem : y ∈ fiveCoefficients.range := by
    rw [hy]
    exact fiveCoefficients.range.sum_mem (fun i _ => principal_in_range (R i) n (hR i) i)
  exact hmem

end ActualSourceHOneFiveSpanning318
