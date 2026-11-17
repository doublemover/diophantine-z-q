module
public import ActualFullPrimarySelmerLowCorank318
public import ActualTwoDescentPontryaginFreeRankOne318
public import BoundedCircleCharacters318
public section
noncomputable section
namespace ActualPontryaginLowCorank318
open ActualFullPrimarySelmerLowCorank318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualPrimaryCharacters318 ActualTwoDescentDiscreteSelmerDual318
open ActualTwoDescentPontryaginRationalCharacters318 ActualTwoDescentPontryaginPadicModule318
open ActualTwoDescentPontryaginFreeRankOne318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentSelmerCharacterFreeRankOne318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- A concrete finite cyclic model of the actual Selmer group gives finite
actual rational-circle characters by bounded values, not by counting maps
into an infinite target. -/
theorem finite_characters_of_cyclic_model (n : ℚ) (hn : n ≠ 0) (k : ℕ)
    (e : actualPrimarySelmer n hn ≃+ ZMod (2^k)) :
    Finite (ActualPrimaryCharacters n hn) := by
  letI : Finite (actualPrimarySelmer n hn) :=
    Finite.of_equiv (ZMod (2^k)) e.symm.toEquiv
  apply BoundedCircleCharacters318.finite_characters k
  intro x
  apply e.injective
  rw [map_nsmul, map_zero]
  simp [nsmul_eq_mul]

/-- The NATIVE compact Pontryagin dual of actual full primary Selmer is
finite or linearly Z2, without assuming the missing global reduced pairing.
This is a genuine full-Selmer low-corank alternative, not a statement about
only one finite Selmer level or the rational-point rank. -/
theorem actual_pontryagin_finite_or_linear_z2 (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    letI := actualPontryaginPadicModule n hn
    Finite (ActualPontryagin n hn) ∨
      Nonempty (Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ℤ_[2]) := by
  letI := actualPontryaginPadicModule n hn
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k, ⟨e⟩⟩ | ⟨e⟩
  · letI := finite_characters_of_cyclic_model n hn k e
    have h : Finite (Additive (ActualPontryagin n hn)) :=
      Finite.of_equiv (ActualPrimaryCharacters n hn)
        (nativeRationalCharacterEquiv n hn).symm.toEquiv
    exact Or.inl h
  · letI := actualCharacterPadicModule n hn
    exact Or.inr ⟨(nativeRationalCharacterLinearEquiv n hn).trans
      (actualPrimaryCharacterLinearEquiv n hn e)⟩

end ActualPontryaginLowCorank318
