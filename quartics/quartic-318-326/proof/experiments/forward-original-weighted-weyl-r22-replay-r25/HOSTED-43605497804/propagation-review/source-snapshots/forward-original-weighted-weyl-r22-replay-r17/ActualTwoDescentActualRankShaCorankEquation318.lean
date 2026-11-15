module
public import ActualTwoDescentActualShaPrueferTwoCard318
public section
noncomputable section
namespace ActualTwoDescentActualRankShaCorankEquation318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaDefinition318
open ActualTwoDescentActualShaReducedDuality318 ActualTwoDescentActualShaZeroPrueferDuality318
open ActualTwoDescentActualShaPrueferTwoCard318 ActualTwoDescentActualShaPrimaryVanishing318
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentFreeRankObstructionEquation318
open ActualTwoDescentActualShaObstructionEquivalence318 ActualTwoDescentEllipticModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Exact r+t=1 with an ACTUAL free Mordell-Weil decomposition and an ACTUAL zero/Prüfer identification of full primary Sha. The missing global duality producer remains a named explicit input. -/
theorem actual_free_rank_plus_sha_corank (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    ∃ r t : ℕ, r+t=1 ∧ ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (Point n ≃+ (Fin r →₀ ℤ) × T) ∧
      ((t=0 ∧ Subsingleton (actualShaPrimary n hn)) ∨
       (t=1 ∧ Nonempty (actualShaPrimary n hn ≃* PrueferTwo))) := by
  obtain ⟨r,hr,T,hT,hfin,he,heq⟩ := actual_free_rank_obstruction_equation n hn hf hb hS
  rw [←actual_sha_obstruction_cardinality] at heq
  rcases actual_sha_zero_or_pruefer_of_duality n hn hf hb hS hdual with hz|⟨hi,hp⟩
  · have hc := actual_sha_two_one_of_primary_trivial n hn hz
    rw [hc,mul_one] at heq
    have hr1 : r=1 := by interval_cases r <;> norm_num at heq ⊢
    exact ⟨r,0,by omega,T,hT,hfin,he,Or.inl ⟨rfl,hz⟩⟩
  · letI := hi
    have hc := actual_infinite_sha_two_card n hn hf hb hS
    rw [hc] at heq
    have hr0 : r=0 := by interval_cases r <;> norm_num at heq ⊢
    exact ⟨r,1,by omega,T,hT,hfin,he,Or.inr ⟨rfl,hp⟩⟩

end ActualTwoDescentActualRankShaCorankEquation318
