module
public import ActualPrimaryTateModel318
public import PrimaryTatePadicNaturality318
public import ActualTwoDescentSelmerPadicAction318
public import Mathlib.LinearAlgebra.Basis.Basic
public section
noncomputable section
namespace ActualPrimaryTateLinearModel318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
open ActualFullPrimarySelmerLowCorank318 PrimaryTateTower318
open PrimaryTatePadicModule318 PrimaryTatePadicNaturality318

/-- The actual Selmer tower receives the natural levelwise residue action,
independently of either branch of the primary-group classification. -/
def actualModule (n : ℚ) (hn : n ≠ 0) :
    Module ℤ_[2] (tower (actualPrimarySelmer n hn)) :=
  naturalModule (actualPrimarySelmer n hn)

/-- This action is also the previously constructed actual primary Selmer
scalar endomorphism at each coordinate. -/
theorem actual_scalar_coordinate (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2])
    (x : tower (actualPrimarySelmer n hn)) (k : ℕ) :
    letI := actualModule n hn
    (a • x).val k =
      ActualTwoDescentSelmerPadicAction318.actualSelmerPadicEnd n hn a (x.val k) := by
  letI := actualModule n hn
  change (PadicInt.toZModPow k a).val • x.val k =
    ActualTwoDescentPrimaryPadicScalar318.primaryPadicScalar
      (ActualTwoDescentSelmerPadicAction318.actual_selmer_primary n hn) a (x.val k)
  exact (ActualTwoDescentPrimaryPadicScalar318.actual_primary_padic_scalar_at_level
    (ActualTwoDescentSelmerPadicAction318.actual_selmer_primary n hn) a k
    (x.val k) (x.property.1 k)).symm

/-- The actual natural Tate module is zero or linearly isomorphic to Z2.
The alternative is NOT selected and every arithmetic hypothesis remains. -/
theorem actual_tate_zero_or_linear_z2 (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    letI := actualModule n hn
    Subsingleton (tower (actualPrimarySelmer n hn)) ∨
      Nonempty (tower (actualPrimarySelmer n hn) ≃ₗ[ℤ_[2]] ℤ_[2]) := by
  letI := actualModule n hn
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k, ⟨e⟩⟩ | ⟨e⟩
  · letI := finite_cyclic_tower_subsingleton k
    left
    constructor
    intro x y
    exact (mapEquiv e).injective (Subsingleton.elim _ _)
  · exact Or.inr ⟨(mapLinearEquiv e).trans naturalPadicEquiv.symm⟩

/-- Equivalently, the unresolved nonzero branch has a genuine singleton
basis for the already defined natural action, not a chosen surrogate group. -/
theorem actual_tate_zero_or_singleton_basis (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    letI := actualModule n hn
    Subsingleton (tower (actualPrimarySelmer n hn)) ∨
      Nonempty (Module.Basis Unit ℤ_[2] (tower (actualPrimarySelmer n hn))) := by
  letI := actualModule n hn
  rcases actual_tate_zero_or_linear_z2 n hn hf hb hS with h | ⟨e⟩
  · exact Or.inl h
  · exact Or.inr ⟨(Module.Basis.singleton Unit ℤ_[2]).map e.symm⟩

end ActualPrimaryTateLinearModel318
