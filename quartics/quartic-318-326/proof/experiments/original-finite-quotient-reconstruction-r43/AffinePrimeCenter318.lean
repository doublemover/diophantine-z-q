module
public import PrimeLocalOriginalField318
public import CenteredDVRRestriction318
public section
noncomputable section
namespace AffinePrimeCenter318
open Polynomial IsLocalRing
variable {B L : Type*} [CommRing B] [IsDomain B] [Field L]
  [Algebra B L] [IsFractionRing B L] [Algebra (RatFunc ℚ) L]
  (P : Ideal B) [P.IsPrime] (f : ℚ[X] →+* B)

@[expose] def coefficients : ℚ[X] →+* Localization.AtPrime P :=
  (algebraMap B (Localization.AtPrime P)).comp f

/-- The center is derived from the original affine prime contraction. -/
lemma center (q : ℚ[X]) (hP : P.comap f = Ideal.span {q}) (a : ℚ[X]) :
    residue (Localization.AtPrime P) (coefficients P f a) = 0 ↔ q ∣ a := by
  rw [residue_eq_zero_iff]
  change algebraMap B (Localization.AtPrime P) (f a) ∈
    maximalIdeal (Localization.AtPrime P) ↔ q ∣ a
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P (f a)]
  change a ∈ P.comap f ↔ q ∣ a
  rw [hP, Ideal.mem_span_singleton]

include f in
/-- Characteristic zero of the ENTIRE actual residue field comes from the
original rational coefficient map, not a supplied residue characteristic. -/
theorem residue_charZero : CharZero (ResidueField (Localization.AtPrime P)) := by
  let φ : ℚ →+* ResidueField (Localization.AtPrime P) :=
    (residue (Localization.AtPrime P)).comp ((coefficients P f).comp C)
  refine ⟨fun m n h => ?_⟩
  apply Nat.cast_injective (R := ℚ)
  apply φ.injective
  simpa only [map_natCast] using h

lemma coefficient_square
    (h : ∀ a, algebraMap B L (f a) =
      algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) a)) (a : ℚ[X]) :
    PrimeLocalOriginalField318.embedding B L P (coefficients P f a) =
      algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) a) := by
  change PrimeLocalOriginalField318.embedding B L P
    (algebraMap B (Localization.AtPrime P) (f a)) = _
  rw [PrimeLocalOriginalField318.embedding_integral, h a]
end AffinePrimeCenter318
