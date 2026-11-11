module
public import ActualOriginalUndampedSingularIntegral318
public section
noncomputable section
namespace ActualOriginalCompleteFourierCount318
open QuadricCRTAssembly318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- All additive frequencies of the ORIGINAL five-coordinate residue
quadric. This includes nonunit frequencies; it is not a primitive-frequency
singular-series coefficient. -/
@[expose] def completeSum (κ : ℤ) (q : ℕ) [NeZero q] : ℂ :=
  ∑ a : ZMod q, ∑ x : Coordinates (ZMod q),
    ZMod.stdAddChar (a * equation (κ : ZMod q) x)

@[expose] def completeAverage (κ : ℤ) (q : ℕ) [NeZero q] : ℂ :=
  completeSum κ q / (q : ℂ)^5

/-- Exact character orthogonality on the ACTUAL original residue space,
including q=1 and all composite nonzero moduli. -/
theorem actual_complete_frequency_sum (κ : ℤ) (q : ℕ) [NeZero q] :
    completeSum κ q = (q : ℂ) * (Nat.card (Quadric (κ : ZMod q)) : ℂ) := by
  classical
  letI : Fintype (Quadric (κ : ZMod q)) :=
    inferInstanceAs (Fintype {x : Coordinates (ZMod q) // equation (κ : ZMod q) x = 0})
  unfold completeSum
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q),ZMod.card]
  rw [←Finset.sum_filter]
  rw [Finset.sum_const,nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun x : Coordinates (ZMod q) =>
      equation (κ : ZMod q) x = 0)).card = Nat.card (Quadric (κ : ZMod q)) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc]
  exact mul_comm _ _

/-- The q^-5 Fourier normalization equals the genuine q^-4 count of
the SAME original quadric. Both normalizing powers are explicit. -/
theorem actual_complete_average_count (κ : ℤ) (q : ℕ) [NeZero q] :
    completeAverage κ q = (Nat.card (Quadric (κ : ZMod q)) : ℂ) / (q : ℂ)^4 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [completeAverage,actual_complete_frequency_sum]
  field_simp [hq]
  <;> ring

theorem actual_prime_power_complete_average (κ : ℤ) (p n : ℕ) [NeZero p] :
    completeAverage κ (p^n) = (ActualFullLocalDensityRecurrence318.volume κ p n : ℂ) := by
  rw [actual_complete_average_count]
  simp only [ActualFullLocalDensityRecurrence318.volume,
    ActualFullLocalDensityRecurrence318.count,Rat.cast_div,Rat.cast_natCast,
    Rat.cast_pow,Nat.cast_pow,pow_mul,Nat.mul_comm]

end ActualOriginalCompleteFourierCount318
