module
public import ActualOriginalLocalProductBounds318
public section
noncomputable section
namespace ActualOddRegularLift318
open QuadricCRTAssembly318 ActualQuadricTaylor318 ActualOriginalModularLift318
open ActualPrimitiveDigitLiftCount318 ActualAmbientQuadricLift318
set_option maxHeartbeats 24000000

/-- At primes dividing kappa, nonzero w alone is NOT a smooth point.
Regular means one of the original first FOUR coordinates is nonzero. -/
@[expose] def Regular {R : Type*} [Zero R] (x : Coordinates R) : Prop :=
  (x.1,x.2.1)≠((0,0),(0,0))

theorem actual_regular_gradient {F : Type*} [Field F] (κ : F) (h2 : (2:F)≠0)
    (x : Coordinates F) (hx : Regular x) : ∃i : Fin 5,gradient κ x i≠0 := by
  by_contra hh
  push_neg at hh
  have ha := hh 0
  have hb := hh 1
  have hc := hh 2
  have hd := hh 3
  have hna : x.1.1=0 := (mul_eq_zero.mp ha).resolve_left h2
  have hnb : x.1.2=0 := (mul_eq_zero.mp hb).resolve_left h2
  have hnc : x.2.1.1=0 := (mul_eq_zero.mp hc).resolve_left (neg_ne_zero.mpr h2)
  have hnd : x.2.1.2=0 := (mul_eq_zero.mp hd).resolve_left (neg_ne_zero.mpr h2)
  exact hx (Prod.ext (Prod.ext hna hnb) (Prod.ext hnc hnd))

/-- The genuine p^4 digit count at an actual regular residue does NOT
require kappa to be a unit. This is the correct odd bad-prime producer. -/
theorem actual_regular_digit_count (κ : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (m : ℤ) (hm : m≠0) (hpm : (p:ℤ)∣m) (x : Coordinates ℤ) (hx : m∣equation κ x)
    (hreg : Regular (mapCoordinates (Int.castRingHom (ZMod p)) x)) :
    Nat.card (DigitLifts κ p m x)=p^4 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hg := actual_regular_gradient (κ:ZMod p)
    (GoodReductionResidue318.two_residue_ne p hp2)
    (mapCoordinates (Int.castRingHom (ZMod p)) x) hreg
  rw [Nat.card_congr (ActualPrimitiveDigitLiftCount318.digitEquiv κ p hp m hm hpm x hx),
    FiniteFiveAffineFiber318.actual_fiber_card _ _ hg,ZMod.card]

theorem actual_regular_ambient_count (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hpm : p∣m) (x : Quadric (κ:ZMod m))
    (hreg : Regular (mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1))) :
    Nat.card (QuadricFiber κ m p x)=p^4 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [←Nat.card_congr (actual_quadric_fiber_equiv κ m p x)]
  exact actual_regular_digit_count κ p hp hp2 (m:ℤ)
    (by exact_mod_cast NeZero.ne m) (by exact_mod_cast hpm)
    (digits m x.1) (actual_base_divides κ m x) hreg

end ActualOddRegularLift318
