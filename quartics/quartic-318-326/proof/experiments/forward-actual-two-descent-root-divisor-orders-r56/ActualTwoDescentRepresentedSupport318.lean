module
public import ActualTwoDescentTorsionUnitData318
public section
noncomputable section
namespace ActualTwoDescentRepresentedSupport318
open ActualTwoDescentLocalUnitData318 ActualTwoDescentLiteralUnitData318
open ActualTwoDescentTorsionUnitData318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentTorsionComparison318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentOddSupportImage318 ActualTwoDescentProducedSupportImages318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Actual local representation of both original Kummer coordinates by a
non-two-torsion point and two nonzero completed-field square multipliers. -/
def RepresentedAt (q n M L : ℕ) [Fact q.Prime] : Prop :=
  ∃ P : LocalPoint (p:=q) n, SquarePair (P.x+3*n) (P.x-n) (M : ℚ_[q]) (L : ℚ_[q])

/-- Genuine local curve representation at a support prime forces the
EXACT finite torsion comparison, with no formal signature hypothesis. -/
theorem actual_represented_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (δ : ZMod 2) (u v : ι → ZMod 2) (i : ι)
    (H : RepresentedAt (p i) (∏ j, p j) (firstRepresentative p δ u) (monomial p v)) :
    ∃ a b : ZMod 2, localCode p δ u v i=a • torsionOne p i+b • torsionTwo p i := by
  obtain ⟨P,HP⟩ := H
  have ht := actual_odd_support_image _ (hp2 i) (hp3 i) (actual_product_support_valuation p hd i) P
  obtain ⟨a,b,Ht⟩ := actual_torsion_unit_data p hd hp2 hp3 i _ _ ht
  have Hr : PairData (P.x+3*(∏ j, p j : ℕ)) (P.x-(∏ j, p j : ℕ)) (localCode p δ u v i) := by
    apply actual_pair_data_transport _ _ (firstRepresentative p δ u) (monomial p v) _ ?_ HP
    exact ⟨actual_first_unit_data p hd hp3 δ u i,actual_monomial_unit_data p hd v i⟩
  exact ⟨a,b,actual_pair_data_unique _ _ _ _ Hr Ht⟩

end ActualTwoDescentRepresentedSupport318
