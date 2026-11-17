module
public import PrimaryTateTower318
public import ActualFullPrimarySelmerLowCorank318
public section
noncomputable section
namespace ActualPrimaryTateModel318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
open ActualFullPrimarySelmerLowCorank318 PrimaryTateTower318

/-- The genuine compatible torsion tower of actual primary Selmer is zero
or is identified with the compatible tower of the literal dyadic Prüfer
model. No canonical Z2 action or rank statement has yet been asserted. -/
theorem actual_tate_model (n : ℚ) (hn : n≠0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n)≤8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    Subsingleton (tower (actualPrimarySelmer n hn)) ∨
      Nonempty (tower (actualPrimarySelmer n hn) ≃+ tower (Additive PrueferTwo)) := by
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k,⟨e⟩⟩ | ⟨e⟩
  · letI := finite_cyclic_tower_subsingleton k
    left
    constructor
    intro x y
    exact (mapEquiv e).injective (Subsingleton.elim _ _)
  · exact Or.inr ⟨mapEquiv e⟩

end ActualPrimaryTateModel318
