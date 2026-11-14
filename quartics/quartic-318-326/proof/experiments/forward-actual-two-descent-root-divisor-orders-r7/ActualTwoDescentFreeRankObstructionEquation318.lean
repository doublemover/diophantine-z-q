module
public import ActualTwoDescentConcreteGlobalAlternative318
public section
noncomputable section
namespace ActualTwoDescentFreeRankObstructionEquation318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentActualMordellWeilStructure318 ActualTwoDescentConcreteLocalObstruction318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentRationalImageCardinality318

/-- For an ACTUAL free/finite Mordell-Weil decomposition, the residual obstruction
satisfies the exact equation2^r*|obstruction|=2. The rank is not guessed from local cardinality. -/
theorem actual_free_rank_obstruction_equation (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hlocal : Nat.card (allPlacesImage n hn)=8) :
    ∃ r : ℕ, r ≤ 1 ∧ ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (Point n ≃+ (Fin r →₀ ℤ) × T) ∧
      2^r*Nat.card (LocalObstruction n hn)=2 := by
  obtain ⟨r,hr,T,hT,hfin,he,hcard⟩ := actual_free_rank_at_most_one n hn hf hbound
  have hprod := actual_rational_obstruction_product n hn
  rw [hcard,hlocal] at hprod
  have hfour : 4*(2^r*Nat.card (LocalObstruction n hn))=8 := by
    calc
      _=(2^r*4)*Nat.card (LocalObstruction n hn) := by ring
      _=8 := hprod
  exact ⟨r,hr,T,hT,hfin,he,by omega⟩

end ActualTwoDescentFreeRankObstructionEquation318
