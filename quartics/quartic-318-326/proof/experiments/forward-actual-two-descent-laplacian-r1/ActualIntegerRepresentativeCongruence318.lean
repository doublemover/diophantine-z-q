module
public import ActualDyadicAmbientLift318
public section
noncomputable section
namespace ActualIntegerRepresentativeCongruence318
open QuadricCRTAssembly318 ActualQuadricTaylor318 ActualOriginalModularLift318 ActualDyadicIntegerLift318
set_option maxHeartbeats 26000000

/-- Actual coordinate congruence gives an INTEGER translate, with a
separate integer displacement for each of the original five coordinates. -/
theorem actual_integer_translate_of_reduction (m : ℕ) (x y : Coordinates ℤ)
    (hxy : mapCoordinates (Int.castRingHom (ZMod m)) x=
      mapCoordinates (Int.castRingHom (ZMod m)) y) :
    ∃h : Coordinates ℤ,y=translate x h (m:ℤ) := by
  have hd (a b : ℤ) (he : (a:ZMod m)=(b:ZMod m)) : (m:ℤ)∣b-a := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (b-a) m).mp
    rw [Int.cast_sub,he,sub_self]
  have ha := congrArg (fun z : Coordinates (ZMod m) => z.1.1) hxy
  have hb := congrArg (fun z : Coordinates (ZMod m) => z.1.2) hxy
  have hc := congrArg (fun z : Coordinates (ZMod m) => z.2.1.1) hxy
  have hd' := congrArg (fun z : Coordinates (ZMod m) => z.2.1.2) hxy
  have hw := congrArg (fun z : Coordinates (ZMod m) => z.2.2) hxy
  obtain ⟨a,ha⟩ := hd _ _ ha
  obtain ⟨b,hb⟩ := hd _ _ hb
  obtain ⟨c,hc⟩ := hd _ _ hc
  obtain ⟨d,hd'⟩ := hd _ _ hd'
  obtain ⟨w,hw⟩ := hd _ _ hw
  refine ⟨((a,b),(c,d),w),?_⟩
  apply Prod.ext
  · apply Prod.ext <;> dsimp [translate] <;> linarith
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [translate] <;> linarith
    · dsimp [translate]
      linarith

/-- The next dyadic congruence test is independent of the choice of
integer representatives of an original even-modulus residue class. -/
theorem actual_even_representative_invariance (κ : ℤ) (m : ℕ) (hm : 2∣m)
    (x y : Coordinates ℤ)
    (hxy : mapCoordinates (Int.castRingHom (ZMod m)) x=
      mapCoordinates (Int.castRingHom (ZMod m)) y) :
    (2*(m:ℤ))∣equation κ x ↔ (2*(m:ℤ))∣equation κ y := by
  obtain ⟨h,rfl⟩ := actual_integer_translate_of_reduction m x y hxy
  exact (actual_even_lift_iff κ (m:ℤ) (by exact_mod_cast hm) x h).symm

/-- In particular canonical ZMod.val digits do not introduce an
unproved sign/carry assumption into the next congruence test. -/
theorem actual_canonical_next_test (κ : ℤ) (m : ℕ) [NeZero m] (hm : 2∣m)
    (x : Coordinates ℤ) :
    (2*(m:ℤ))∣equation κ (digits m (mapCoordinates (Int.castRingHom (ZMod m)) x)) ↔
      (2*(m:ℤ))∣equation κ x := by
  apply actual_even_representative_invariance κ m hm
  exact digits_reduce m _

end ActualIntegerRepresentativeCongruence318
