module
public import ActualTwoDescentSelmerPadicAction318
public section
noncomputable section
namespace ActualTwoDescentSelmerCharacterFreeRankOne318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentActualPrimaryCharacters318
open ActualTwoDescentSelmerPadicAction318 ActualTwoDescentDyadicCharacterEndomorphisms318
open ActualTwoDescentPrueferLevelCoordinates318 ActualTwoDescentPrueferPadicEndomorphisms318
open ActualTwoDescentPrueferEndResidues318 ActualTwoDescentPrimaryPadicNaturality318
open ActualTwoDescentFullPrimarySelmerPruefer318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentActualShaReducedDuality318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

lemma actual_character_end_scalar (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (a : ℤ_[2]) (f : ActualPrimaryCharacters n hn) :
    dyadicCharacterEnd (primaryCharacterTransport n hn e (f.comp (actualSelmerPadicEnd n hn a)))=
      dyadicCharacterEnd (primaryCharacterTransport n hn e f)*padicToPrueferEnd a := by
  ext x
  apply Subtype.ext
  change Multiplicative.ofAdd (f (actualSelmerPadicEnd n hn a (e.symm x)))=
    Multiplicative.ofAdd (f (e.symm (padicToPrueferEnd a x)))
  have h := actual_selmer_padic_equiv_natural n hn e a (e.symm x)
  rw [e.apply_symm_apply] at h
  exact congrArg (fun z => Multiplicative.ofAdd (f z)) ((e.eq_symm_apply).mp h)

def actualPrimaryCharacterLinearEquiv (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) :
    letI := actualCharacterPadicModule n hn
    ActualPrimaryCharacters n hn ≃ₗ[ℤ_[2]] ℤ_[2] := by
  letI := actualCharacterPadicModule n hn
  refine { toAddEquiv := (primaryCharacterTransport n hn e).trans dyadicCharacterPadicEquiv
           map_smul' := ?_ }
  intro a f
  change prueferEndToPadic
    (dyadicCharacterEnd (primaryCharacterTransport n hn e (f.comp (actualSelmerPadicEnd n hn a))))=
      a*prueferEndToPadic (dyadicCharacterEnd (primaryCharacterTransport n hn e f))
  rw [actual_character_end_scalar,map_mul,actual_pruefer_end_padic_right_inverse,mul_comm]

/-- The ACTUAL rational-circle character module is genuinely free of rank
one over native Z_2 with its natural scalar action, conditional on the actual
global reduced pairing. No rational-rank branch or analytic rank is selected. -/
theorem actual_selmer_character_free_rank_one (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    letI := actualCharacterPadicModule n hn
    Nonempty (ActualPrimaryCharacters n hn ≃ₗ[ℤ_[2]] ℤ_[2]) := by
  obtain ⟨e⟩ := actual_full_primary_selmer_pruefer n hn hf hb hS hdual
  exact ⟨actualPrimaryCharacterLinearEquiv n hn e⟩

end ActualTwoDescentSelmerCharacterFreeRankOne318
