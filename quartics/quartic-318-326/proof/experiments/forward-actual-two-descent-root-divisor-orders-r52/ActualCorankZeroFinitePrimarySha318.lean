module
public import ActualFullSelmerCorank318
import all ActualFullSelmerCorank318
public import ActualTwoDescentPrimarySelmerShaSurjectivity318
public section
noncomputable section
namespace ActualCorankZeroFinitePrimarySha318
open ActualFullSelmerCorank318 ActualFullPrimarySelmerLowCorank318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentActualShaPrimary318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPadicModule318
open ActualTwoDescentPontryaginFreeRankOne318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentSelmerCharacterFreeRankOne318
open ActualTwoDescentPrimarySelmerToSha318 ActualTwoDescentPrimarySelmerShaSurjectivity318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- In the actual low-corank classification, zero full-Selmer corank rules
out the Pruefer branch. This is a statement about the whole primary Selmer
group, not just a single finite-level Selmer group or rational-point rank. -/
theorem actual_primary_selmer_finite_of_corank_zero (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8)
    (h0 : actualFullSelmerCorank n hn = 0) :
    Finite (actualPrimarySelmer n hn) := by
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k, ⟨e⟩⟩ | ⟨e⟩
  · exact Finite.of_equiv (ZMod (2^k)) e.symm.toEquiv
  · letI := actualPontryaginPadicModule n hn
    letI := actualCharacterPadicModule n hn
    let d : Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ℤ_[2] :=
      (nativeRationalCharacterLinearEquiv n hn).trans
        (actualPrimaryCharacterLinearEquiv n hn e)
    have h1 : actualFullSelmerCorank n hn = 1 := by
      change Module.rank ℤ_[2] (Additive (ActualPontryagin n hn)) = 1
      rw [d.rank_eq, CommSemiring.rank_self]
    exact False.elim (zero_ne_one (h0.symm.trans h1))

/-- The actual primary Selmer-to-Sha map is surjective, so finiteness of
its source implies finiteness of the full 2-primary Sha subgroup. No
finiteness assumption on rational points or reduced duality is needed. -/
theorem actual_primary_sha_finite_of_finite_selmer (n : ℚ) (hn : n ≠ 0)
    [Finite (actualPrimarySelmer n hn)] : Finite (actualShaPrimary n hn) := by
  have h : Finite (Additive (actualShaPrimary n hn)) :=
    Finite.of_surjective (primarySelmerToSha n hn)
      (actual_primary_selmer_sha_surjective n hn)
  exact h

/-- The corank-zero branch has finite FULL 2-primary Sha under the same
actual arithmetic hypotheses. This does not assert Sha vanishing,
finiteness of its other primary parts, or anything about corank one. -/
theorem actual_primary_sha_finite_of_corank_zero (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8)
    (h0 : actualFullSelmerCorank n hn = 0) :
    Finite (actualShaPrimary n hn) := by
  letI := actual_primary_selmer_finite_of_corank_zero n hn hf hb hS h0
  exact actual_primary_sha_finite_of_finite_selmer n hn

end ActualCorankZeroFinitePrimarySha318
