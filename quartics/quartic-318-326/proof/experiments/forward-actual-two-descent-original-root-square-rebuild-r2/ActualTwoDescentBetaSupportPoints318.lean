module
public import ActualTwoDescentBetaSupportSquares318
public section
noncomputable section
namespace ActualTwoDescentBetaSupportPoints318
open ActualTwoDescentBetaSupportSquares318 ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentPrimeLaplacian318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Every support-prime beta class in the actual kernel is represented by
an ACTUAL completed-field curve point, with both original Kummer equations.
This supplies local sufficiency at the odd support primes, not just signs. -/
theorem actual_beta_support_points {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (b : ι → ZMod 2) (hK : laplacian p *ᵥ b=0) :
    ∀ i, Nonempty (LocalKummerPoint (p:=p i) (monomial p b) (∏ j, p j)) := by
  have hn0 : (∏ j, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun j _ => (Fact.out : (p j).Prime).ne_zero)
  intro i
  rcases actual_beta_support_squarecases p hd hp2 b hK i with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
  · exact actual_local_kummer_of_square _ _ r hr he.symm
  · exact actual_local_kummer_of_first_torsion _ _ hn0 r hr he

end ActualTwoDescentBetaSupportPoints318
