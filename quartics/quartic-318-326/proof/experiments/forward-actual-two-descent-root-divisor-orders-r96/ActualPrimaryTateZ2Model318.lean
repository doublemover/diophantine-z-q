module
public import ActualPrimaryTateModel318
public import PrueferTateResidueBridge318
public section
noncomputable section
namespace ActualPrimaryTateZ2Model318
open ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
open PrimaryTateTower318

/-- The actual full primary Selmer tower is either zero or additively Z2.
The hypotheses and unresolved branch choice are retained. This is not a
pointwise 2-converse, finiteness of Sha, or a positive Mordell-Weil rank claim. -/
theorem actual_tate_zero_or_z2 (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    Subsingleton (tower (actualPrimarySelmer n hn)) ∨
      Nonempty (tower (actualPrimarySelmer n hn) ≃+ ℤ_[2]) := by
  rcases ActualPrimaryTateModel318.actual_tate_model n hn hf hb hS with h | ⟨e⟩
  · exact Or.inl h
  · exact Or.inr ⟨e.trans PrueferTateResidueBridge318.padicEquiv.symm⟩

end ActualPrimaryTateZ2Model318
