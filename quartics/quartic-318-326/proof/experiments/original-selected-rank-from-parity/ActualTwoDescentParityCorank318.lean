module
public import ActualTwoDescentPontryaginFreeRankOne318
public import ActualTwoDescentActualShaPrimaryTwo318
public import ActualTwoDescentActualShaRankAlternative318
public import ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
public import ActualTwoDescentInfiniteRankSelmerPruefer318
public import ActualTwoDescentPrueferLevelCoordinates318
public import ActualTwoDescentPrueferClassification318
import all ActualTwoDescentPrimaryPowerLevels318
public section
noncomputable section

namespace ActualTwoDescentParityCorank318
open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentActualShaRankAlternative318
open ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
open ActualTwoDescentInfiniteRankSelmerPruefer318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentPrueferLevelCoordinates318
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentAdditivePrimaryLevels318
open ActualTwoDescentPrueferClassification318 ActualTwoDescentFullPrimarySelmerTorsion318
open ActualTwoDescentSelmerPadicAction318 ActualTwoDescentSelmerCharacterFreeRankOne318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPadicModule318
open ActualTwoDescentPontryaginFreeRankOne318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 16000000

/-- Transport literal kernels of multiplication by the SAME power of two. -/
def killedCongr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (k : ℕ) : additivePowerLevel A k ≃ additivePowerLevel B k where
  toFun x := ⟨e x.val,by
    change (2^k) • e x.val = 0
    rw [←map_nsmul,x.property,map_zero]⟩
  invFun x := ⟨e.symm x.val,by
    change (2^k) • e.symm x.val = 0
    rw [←map_nsmul,x.property,map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)

/-- The subgroup killed by 2 in the genuine all-place full primary
Selmer group has order TWO, without any arithmetic parity or pairing.
The existing finite/infinite rational-point alternative is used only
by cases, not resolved. -/
theorem actual_full_primary_two_card (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    Nat.card (additivePowerLevel (actualPrimarySelmer n hn) 1) = 2 := by
  rcases actual_sha_rank_alternative n hn hf hb hS with ⟨_, htwo, hfin⟩ | ⟨_, _, hinf⟩
  · letI := hfin
    let e := killedCongr (finiteRankPrimarySelmerEquiv n hn) 1
    let f := additivePowerLevelEquiv (Additive (actualShaPrimary n hn)) 1
    calc
      Nat.card (additivePowerLevel (actualPrimarySelmer n hn) 1) =
          Nat.card (additivePowerLevel (Additive (actualShaPrimary n hn)) 1) :=
        Nat.card_congr e
      _ = Nat.card (powerLevel (actualShaPrimary n hn) 1) := Nat.card_congr f.toEquiv
      _ = Nat.card (ActualTwoDescentActualShaDefinition318.actualShaTwo n hn) :=
        Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv
      _ = 2 := htwo
  · letI := hinf
    obtain ⟨e⟩ := actual_infinite_rank_selmer_pruefer n hn hf hb hS
    exact (Nat.card_congr (killedCongr e 1)).trans (by
      simpa only [pow_one] using actual_pruefer_level_card 1)

/-- Weakest input needed from odd 2-primary Selmer parity: its actual
full group is infinite. The same literal compact Pontryagin dual now
becomes free of rank one, without finite Sha or any reduced pairing. -/
theorem native_free_of_infinite (n : ℚ) (hn : n ≠ 0)
    (hcard : Nat.card (additivePowerLevel (actualPrimarySelmer n hn) 1) = 2)
    (hInf : Infinite (actualPrimarySelmer n hn)) :
    letI := actualPontryaginPadicModule n hn
    Nonempty (Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ℤ_[2]) := by
  letI := actualPontryaginPadicModule n hn
  letI := actualCharacterPadicModule n hn
  letI : Infinite (Multiplicative (actualPrimarySelmer n hn)) := hInf
  have hp : IsPGroup 2 (Multiplicative (actualPrimarySelmer n hn)) := by
    intro x
    exact actual_primary_selmer_two_primary n hn x.toAdd
  have hCard : Nat.card (powerLevel (Multiplicative (actualPrimarySelmer n hn)) 1) = 2 :=
    (Nat.card_congr (additivePowerLevelEquiv (actualPrimarySelmer n hn) 1).toEquiv).symm.trans hcard
  have hFin : Finite (powerLevel (Multiplicative (actualPrimarySelmer n hn)) 1) :=
    Nat.finite_of_card_ne_zero (by rw [hCard] <;> decide)
  obtain ⟨e⟩ := actual_infinite_primary_pruefer hp hFin (le_of_eq hCard)
  let ea : actualPrimarySelmer n hn ≃+ PrueferAdd :=
    { toEquiv := e.toEquiv
      map_add' x y := e.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  exact ⟨(nativeRationalCharacterLinearEquiv n hn).trans
    (actualPrimaryCharacterLinearEquiv n hn ea)⟩

end ActualTwoDescentParityCorank318

#print axioms ActualTwoDescentParityCorank318.actual_full_primary_two_card
#print axioms ActualTwoDescentParityCorank318.native_free_of_infinite
