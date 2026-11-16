module
public import ActualTwoDescentFiniteHalvingGroup318
public section
noncomputable section
namespace ActualTwoDescentFiniteIdentityClassHalving318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteHalvingRoots318
open ActualTwoDescentFiniteHalvingCoordinates318 ActualTwoDescentFiniteHalvingGroup318
open ActualTwoDescentTorsionSquarePairs318
variable [DecidableEq K]

/-- Identity-class membership produces an actual half, not a formal squareclass. -/
theorem actual_identity_class_half (n x y : K) (hn : n ≠ 0)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (H : SquarePair (x+3*n) (x-n) 1 1) :
    ∃ Q : Point n, Q ≠ 0 ∧ Q+Q=point n x y hn hc := by
  obtain ⟨a,b,c,ha0,hb0,hc0,ha,hb,hcc,hprod⟩ := actual_halving_roots n x y hx hB hA hc H
  refine ⟨point n (halfX x a b c) (halfY a b c) hn (half_curve n x a b c ha hb hcc),
    point_ne_zero _ _ _ _ _,?_⟩
  exact actual_half_add_self n x y a b c hn hc ha hb hcc hprod

end ActualTwoDescentFiniteIdentityClassHalving318
