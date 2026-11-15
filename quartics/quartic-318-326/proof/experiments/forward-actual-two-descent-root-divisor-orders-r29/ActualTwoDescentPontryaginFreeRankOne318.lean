module
public import ActualTwoDescentPontryaginPadicModule318
public section
noncomputable section
namespace ActualTwoDescentPontryaginFreeRankOne318
set_option maxHeartbeats 16000000
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginRationalCharacters318
open ActualTwoDescentPontryaginPadicModule318 ActualTwoDescentActualPrimaryCharacters318
open ActualTwoDescentSelmerPadicAction318 ActualTwoDescentSelmerCharacterFreeRankOne318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentActualShaReducedDuality318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def nativeRationalCharacterLinearEquiv (n : ℚ) (hn : n ≠ 0) :
    letI := actualPontryaginPadicModule n hn
    letI := actualCharacterPadicModule n hn
    Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ActualPrimaryCharacters n hn := by
  letI := actualPontryaginPadicModule n hn
  letI := actualCharacterPadicModule n hn
  exact { toAddEquiv := nativeRationalCharacterEquiv n hn
          map_smul' := fun a f => actual_native_character_scalar n hn a f.toMul }

/-- The NATIVE compact Pontryagin dual of ACTUAL discrete full2-primary
Selmer, with its natural2-adic action, is genuinely free of rank one.
The global reduced pairing is still explicit; no rational rank is selected. -/
theorem actual_native_pontryagin_free_rank_one (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    letI := actualPontryaginPadicModule n hn
    Nonempty (Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ℤ_[2]) := by
  letI := actualPontryaginPadicModule n hn
  letI := actualCharacterPadicModule n hn
  obtain ⟨e⟩ := actual_selmer_character_free_rank_one n hn hf hb hS hdual
  exact ⟨(nativeRationalCharacterLinearEquiv n hn).trans e⟩

end ActualTwoDescentPontryaginFreeRankOne318
