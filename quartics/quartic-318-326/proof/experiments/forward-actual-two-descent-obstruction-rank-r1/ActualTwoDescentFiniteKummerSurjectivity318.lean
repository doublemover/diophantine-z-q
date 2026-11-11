module
public import ActualTwoDescentFiniteSquareclassCardinality318
public section
noncomputable section
namespace ActualTwoDescentFiniteKummerSurjectivity318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteKummerHom318
open ActualTwoDescentFiniteEllipticDoubleQuotient318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentFinitePointCardinality318 ActualTwoDescentFiniteSquareclassCardinality318
open ActualTwoDescentDoublingIndexTransport318
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)] [DecidableEq K] [Finite K]

lemma actual_finite_elliptic_quotient_card (n : K) (hn : n ≠ 0) : Nat.card (DoubleQuotient n)=4 := by
  letI : Finite (Point n) := actual_finite_points n
  rw [←actual_tagged_doubles_index (Point n)]
  change (nsmulAddMonoidHom (α:=Point n) 2).range.index=4
  rw [AddSubgroup.index_range]
  exact actual_doubling_kernel_card n hn

/-- Actual finite-field Kummer surjectivity follows from the actual group and
its four-element doubling kernel, not a formal local-image assertion. -/
theorem actual_finite_kummer_surjective (n : K) (hn : n ≠ 0) :
    Function.Surjective (ellipticKummerInjection n hn) := by
  have hc : Nat.card (DoubleQuotient n)=Nat.card (SquareClass K × SquareClass K) := by
    rw [actual_finite_elliptic_quotient_card n hn,Nat.card_prod,actual_finite_squareclass_card]
    norm_num
  exact ((Nat.bijective_iff_injective_and_card (ellipticKummerInjection n hn)).mpr
    ⟨actual_elliptic_kummer_injective n hn,hc⟩).2

/-- Every pair of nonzero finite-field squareclasses has an ACTUAL elliptic representative. -/
theorem actual_finite_kummer_representative (n : K) (hn : n ≠ 0)
    (z : SquareClass K × SquareClass K) : ∃ P : Point n, kummerClass n hn P=z := by
  obtain ⟨q,rfl⟩ := actual_finite_kummer_surjective n hn z
  refine QuotientGroup.induction_on q ?_
  intro P
  exact ⟨P.toAdd,rfl⟩

end ActualTwoDescentFiniteKummerSurjectivity318
