module
public import CanonicalDVRQuotientLength318
public import Mathlib.NumberTheory.RamificationInertia.Galois
public section
noncomputable section
namespace OriginalPrimeOrderInertia318
open Polynomial IsDiscreteValuationRing IsLocalRing
variable {B : Type*} [CommRing B] [IsDomain B] [Algebra ℚ[X] B]
  (P : Ideal B) [P.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime P)]
  (q : ℚ[X]) (hcenter : P.under ℚ[X] = Ideal.span {q})
  (hne : algebraMap ℚ[X] (Localization.AtPrime P) q ≠ 0)

include hcenter hne in
/-- Match Mathlib's actual ideal ramification index with the canonical order
in the literal prime localization. Both use the SAME mapped prime ideal. -/
theorem canonical_order :
    addVal (Localization.AtPrime P) (algebraMap ℚ[X] (Localization.AtPrime P) q) =
      (P.ramificationIdx ℚ[X] : ENat) := by
  have hidx : P.ramificationIdx ℚ[X] =
      (addVal (Localization.AtPrime P) (algebraMap ℚ[X] (Localization.AtPrime P) q)).toNat := by
    rw [Ideal.ramificationIdx_def, hcenter, Ideal.map_span, Set.image_singleton,
      CanonicalDVRQuotientLength318.length_span _ _ hne]
  have ht : addVal (Localization.AtPrime P)
      (algebraMap ℚ[X] (Localization.AtPrime P) q) ≠ ⊤ :=
    fun h => hne ((addVal_eq_top_iff (R := Localization.AtPrime P)).mp h)
  exact (ENat.natCast_toNat ht).symm.trans (congrArg (fun n : ℕ => (n : ENat)) hidx.symm)

variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G ℚ[X] B] [Module.Finite ℚ[X] B] [Module.Flat ℚ[X] B]
  [(Ideal.span {q}).IsPrime]
  [Algebra.HasSeparableResidueFieldsAt ℚ[X] B (Ideal.span {q})]

include hcenter hne in
/-- The full ORIGINAL ideal-inertia group determines the canonical local
order. Finite flatness, actual invariants and separable residues are required
by the cardinality theorem and retained here explicitly. -/
theorem order_eq_inertia_card :
    addVal (Localization.AtPrime P) (algebraMap ℚ[X] (Localization.AtPrime P) q) =
      (Nat.card (P.inertia G) : ENat) := by
  letI : P.LiesOver (Ideal.span {q}) := ⟨hcenter.symm⟩
  rw [canonical_order P q hcenter hne,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {q}) P G,
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Ideal.span {q}) P]
end OriginalPrimeOrderInertia318
