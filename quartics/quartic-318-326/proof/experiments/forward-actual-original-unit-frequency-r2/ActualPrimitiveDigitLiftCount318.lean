module
public import ActualOriginalModularLift318
public section
noncomputable section
namespace ActualPrimitiveDigitLiftCount318
open QuadricCRTAssembly318 ActualQuadricTaylor318 ActualOriginalModularLift318
open FiniteFiveAffineFiber318
set_option maxHeartbeats 20000000

@[expose] def DigitLifts (κ : ℤ) (p : ℕ) (m : ℤ) (x : Coordinates ℤ) :=
  {h : Coordinates (ZMod p) // ((p:ℤ)*m)∣equation κ (translate x (digits p h) m)}

/-- Actual original digit lifts are explicitly equivalent to the affine
hyperplane given by the genuine gradient and the true offset Q(x)/m. -/
@[expose] def digitEquiv (κ : ℤ) (p : ℕ) (hp : p.Prime) (m : ℤ) (hm : m≠0)
    (hpm : (p:ℤ)∣m) (x : Coordinates ℤ) (hx : m∣equation κ x) :
    letI : Fact p.Prime := ⟨hp⟩
    DigitLifts κ p m x ≃
      Fiber (gradient (κ:ZMod p) (mapCoordinates (Int.castRingHom (ZMod p)) x))
        (-(offset κ x m:ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let e := coordinateEquiv (ZMod p)
  refine {
    toFun := fun h => ⟨e h.1,?_⟩
    invFun := fun v => ⟨e.symm v.1,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change (∑i,gradient (κ:ZMod p) (mapCoordinates (Int.castRingHom (ZMod p)) x) i*
      vector h.1 i)= -(offset κ x m:ZMod p)
    rw [←derivative_sum]
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using (actual_lift_iff κ p m hm hpm x hx h.1).mp h.2
  · apply (actual_lift_iff κ p m hm hpm x hx (e.symm v.1)).mpr
    rw [derivative_sum]
    have he : vector (e.symm v.1)=v.1 := e.apply_symm_apply v.1
    rw [he,v.2]
    exact add_neg_cancel _
  · intro h
    apply Subtype.ext
    exact e.symm_apply_apply h.1
  · intro v
    apply Subtype.ext
    exact e.apply_symm_apply v.1

/-- Every primitive original residue at a good odd prime has exactly
p^4 genuine digit lifts satisfying the ORIGINAL quadratic congruence.
The affine pivot is constructed from its nonzero original gradient. -/
theorem actual_good_digit_lift_count (κ : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (hκ : ¬(p:ℤ)∣κ) (m : ℤ) (hm : m≠0) (hpm : (p:ℤ)∣m)
    (x : Coordinates ℤ) (hx : m∣equation κ x)
    (hprim : mapCoordinates (Int.castRingHom (ZMod p)) x≠((0,0),(0,0),0)) :
    Nat.card (DigitLifts κ p m x)=p^4 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk : (κ:ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  have hg := original_gradient_nonzero (κ:ZMod p) hk
    (GoodReductionResidue318.two_residue_ne p hp2)
    (mapCoordinates (Int.castRingHom (ZMod p)) x) hprim
  rw [Nat.card_congr (digitEquiv κ p hp m hm hpm x hx),actual_fiber_card _ _ hg,ZMod.card]

/-- The exact p^4 producer applies at every original exponent e>=1.
It does not yet identify digit tuples with all ambient p-adic residues;
that comparison is a separate finite base-p reconstruction step. -/
theorem actual_prime_power_digit_count (κ : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (hκ : ¬(p:ℤ)∣κ) (e : ℕ) (he : 1≤e) (x : Coordinates ℤ)
    (hx : (p:ℤ)^e∣equation κ x)
    (hprim : mapCoordinates (Int.castRingHom (ZMod p)) x≠((0,0),(0,0),0)) :
    Nat.card {h : Coordinates (ZMod p) //
      (p:ℤ)^(e+1)∣equation κ (translate x (digits p h) ((p:ℤ)^e))}=p^4 := by
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hd : (p:ℤ)∣(p:ℤ)^e := dvd_pow_self _ (by omega)
  have hh := actual_good_digit_lift_count κ p hp hp2 hκ ((p:ℤ)^e)
    (pow_ne_zero e hp0) hd x hx hprim
  simpa only [DigitLifts,pow_succ,mul_comm] using hh

end ActualPrimitiveDigitLiftCount318
