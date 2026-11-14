module
public import ActualTwoDescentFiniteTorsionLevelGrowth318
public section
noncomputable section
namespace ActualTwoDescentBoundedNaturalStabilization318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

/-- A bounded monotone natural sequence stabilizes, with an actual finite maximum of chosen value witnesses. -/
lemma actual_bounded_monotone_stabilizes (h : ℕ → ℕ) (hm : Monotone h) (C : ℕ)
    (hb : ∀ k, h k ≤ C) : ∃ N : ℕ, ∀ k, N ≤ k → h k=h N := by
  classical
  let v (k : ℕ) : Fin (C+1) := ⟨h k,Nat.lt_succ_of_le (hb k)⟩
  let chooseIndex (a : Fin (C+1)) : ℕ := if ha : ∃ k, v k=a then Classical.choose ha else 0
  have hs (k : ℕ) : v (chooseIndex (v k))=v k := by
    dsimp only [chooseIndex]
    rw [dif_pos ⟨k,rfl⟩]
    exact Classical.choose_spec (show ∃ j, v j=v k from ⟨k,rfl⟩)
  let N := Finset.univ.sup chooseIndex
  have hmax (k : ℕ) : h k ≤ h N := by
    have hk : chooseIndex (v k) ≤ N := Finset.le_sup (Finset.mem_univ _)
    have he : h (chooseIndex (v k))=h k := congrArg Fin.val (hs k)
    rw [←he]
    exact hm hk
  exact ⟨N,fun k hk => Nat.le_antisymm (hmax k) (hm hk)⟩

end ActualTwoDescentBoundedNaturalStabilization318
