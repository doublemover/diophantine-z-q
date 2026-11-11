module
public import ActualCoordinateLiftFiber318
public section
noncomputable section
namespace ActualAmbientQuadricLift318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualQuadricTaylor318
open ActualCoordinateLiftFiber318 ActualPrimitiveDigitLiftCount318
set_option maxHeartbeats 22000000

/-- The actual SINGLE-modulus original quadric fiber over x. -/
@[expose] def QuadricFiber (κ : ℤ) (m p : ℕ) (x : Quadric (κ:ZMod m)) :=
  {y : Quadric (κ:ZMod (m*p)) //
    mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y.1=x.1}

lemma actual_quadric_condition (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (x : Coordinates (ZMod m)) (h : Coordinates (ZMod p)) :
    equation (κ:ZMod (m*p)) (coordinateFiberEquiv m p x h).1=0 ↔
      ((p:ℤ)*(m:ℤ))∣equation κ (translate (digits m x) (digits p h) (m:ℤ)) := by
  rw [actual_integer_lift_formula]
  have he := equation_map (Int.castRingHom (ZMod (m*p))) κ
    (translate (digits m x) (digits p h) (m:ℤ))
  rw [he]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.cast_mul,mul_comm]

/-- The digit-count producer is now consumed at the genuine ambient
quadric fiber. Surjectivity covers EVERY original residue above x. -/
@[expose] def actual_quadric_fiber_equiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (x : Quadric (κ:ZMod m)) :
    DigitLifts κ p (m:ℤ) (digits m x.1) ≃ QuadricFiber κ m p x := by
  let e := coordinateFiberEquiv m p x.1
  refine {
    toFun := fun h => ⟨⟨(e h.1).1,?_⟩,(e h.1).2⟩
    invFun := fun y => ⟨e.symm ⟨y.1.1,y.2⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (actual_quadric_condition κ m p x.1 h.1).mpr h.2
  · apply (actual_quadric_condition κ m p x.1 (e.symm ⟨y.1.1,y.2⟩)).mp
    have he := congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1,y.2⟩)
    change equation (κ:ZMod (m*p)) (e (e.symm ⟨y.1.1,y.2⟩)).1=0
    rw [he]
    exact y.1.2
  · intro h
    apply Subtype.ext
    exact e.symm_apply_apply h.1
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1,y.2⟩)

lemma actual_base_divides (κ : ℤ) (m : ℕ) [NeZero m] (x : Quadric (κ:ZMod m)) :
    (m:ℤ)∣equation κ (digits m x.1) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
  have he := equation_map (Int.castRingHom (ZMod m)) κ (digits m x.1)
  rw [digits_reduce] at he
  exact he.symm.trans x.2

/-- Exact p^4 count of ALL original ambient quadric residues above a
primitive original base class, for every nonzero m divisible by p. -/
theorem actual_ambient_quadric_lift_count (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m)
    (x : Quadric (κ:ZMod m))
    (hprim : mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)≠((0,0),(0,0),0)) :
    Nat.card (QuadricFiber κ m p x)=p^4 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [←Nat.card_congr (actual_quadric_fiber_equiv κ m p x)]
  exact actual_good_digit_lift_count κ p hp hp2 hκ (m:ℤ)
    (by exact_mod_cast (NeZero.ne m)) (by exact_mod_cast hpm)
    (digits m x.1) (actual_base_divides κ m x) hprim

end ActualAmbientQuadricLift318
