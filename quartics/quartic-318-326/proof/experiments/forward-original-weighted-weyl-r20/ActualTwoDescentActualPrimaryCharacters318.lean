module
public import ActualTwoDescentDyadicCharacterEndomorphisms318
public section
noncomputable section
namespace ActualTwoDescentActualPrimaryCharacters318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentFullPrimarySelmerPruefer318
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentPrueferLevelCoordinates318
open ActualTwoDescentDyadicCharacterEndomorphisms318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentActualShaReducedDuality318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Characters of the independently defined actual all-place Selmer group. -/
abbrev ActualPrimaryCharacters (n : ℚ) (hn : n ≠ 0) :=
  actualPrimarySelmer n hn →+ AddCircle (1 : ℚ)

def primaryCharacterTransport (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) :
    ActualPrimaryCharacters n hn ≃+ DyadicCharacter where
  toFun f := f.comp e.symm.toAddMonoidHom
  invFun f := f.comp e.toAddMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl

/-- The ACTUAL algebraic2-primary character group is native additive Z_2.
This is not silently relabeled as a topological Pontryagin-duality theorem. -/
theorem actual_primary_character_padic (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    Nonempty (ActualPrimaryCharacters n hn ≃+ ℤ_[2]) := by
  obtain ⟨e⟩ := actual_full_primary_selmer_pruefer n hn hf hb hS hdual
  exact ⟨(primaryCharacterTransport n hn e).trans dyadicCharacterPadicEquiv⟩

end ActualTwoDescentActualPrimaryCharacters318
