module
public import ActualTwoDescentLiteralUnitData318
public section
noncomputable section
namespace ActualTwoDescentTorsionUnitData318
open ActualTwoDescentLocalUnitData318 ActualTwoDescentLiteralUnitData318
open ActualTwoDescentTorsionComparison318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Both original coordinates carry actual completed-field unit data. -/
def PairData {q : ℕ} [Fact q.Prime] (A B : ℚ_[q]) (s : Signature) : Prop :=
  UnitData A s.1.1 s.1.2 ∧ UnitData B s.2.1 s.2.2

lemma actual_pair_data_unique {q : ℕ} [Fact q.Prime] (A B : ℚ_[q])
    (s t : Signature) (H : PairData A B s) (G : PairData A B t) : s=t := by
  obtain ⟨h1,h2⟩ := actual_unit_data_unique A _ _ _ _ H.1 G.1
  obtain ⟨h3,h4⟩ := actual_unit_data_unique B _ _ _ _ H.2 G.2
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

lemma actual_pair_data_transport {q : ℕ} [Fact q.Prime] (A B c d : ℚ_[q])
    (s : Signature) (H : PairData c d s) (G : SquarePair A B c d) : PairData A B s := by
  obtain ⟨r,t,hr,ht,hA,hB⟩ := G
  rw [hA,hB]
  exact ⟨actual_unit_data_square_scale _ _ hr _ _ H.1,
    actual_unit_data_square_scale _ _ ht _ _ H.2⟩

/-- The four ACTUAL torsion squareclasses have exactly the retained
finite signatures. The negative second coordinate and its unit bit are
computed through actual local-unit multiplication. -/
theorem actual_torsion_unit_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3) (i : ι)
    (A B : ℚ_[p i]) (H : TorsionPair (∏ j, p j : ℕ) A B) :
    ∃ a b : ZMod 2, PairData A B (a • torsionOne p i+b • torsionTwo p i) := by
  have h1 := actual_unit_data_one (p:=p i)
  have hN := actual_full_product_unit_data p hd i
  have h3 := actual_three_unit_data (p i) (hp3 i)
  have hm := actual_minus_unit_data (p i) (hp2 i)
  have hnN : UnitData (p:=p i) (-((∏ j, p j : ℕ) : ℚ_[p i])) 1 (parity p i+row p i) := by
    simpa only [neg_one_mul,zero_add,parity] using actual_unit_data_mul _ _ _ _ _ _ hm hN
  have h3N : UnitData (p:=p i) (3*((∏ j, p j : ℕ) : ℚ_[p i])) 1 (lambda p i+row p i) := by
    simpa only [zero_add,lambda] using actual_unit_data_mul _ _ _ _ _ _ h3 hN
  rcases H with H | H | H | H
  · refine ⟨0,0,?_⟩
    apply actual_pair_data_transport _ _ 1 1 _ ?_ H
    simpa [PairData,torsionOne,torsionTwo] using (And.intro h1 h1)
  · refine ⟨1,0,?_⟩
    apply actual_pair_data_transport _ _ (∏ j, p j : ℕ) 1 _ ?_ H
    simpa [PairData,torsionOne,torsionTwo] using (And.intro hN h1)
  · refine ⟨0,1,?_⟩
    apply actual_pair_data_transport _ _ 3 (-((∏ j, p j : ℕ) : ℚ_[p i])) _ ?_ H
    simpa [PairData,torsionOne,torsionTwo,lambda] using (And.intro h3 hnN)
  · refine ⟨1,1,?_⟩
    apply actual_pair_data_transport _ _ (3*((∏ j, p j : ℕ) : ℚ_[p i])) (-((∏ j, p j : ℕ) : ℚ_[p i])) _ ?_ H
    simpa [PairData,torsionOne,torsionTwo,add_comm] using (And.intro h3N hnN)

end ActualTwoDescentTorsionUnitData318
