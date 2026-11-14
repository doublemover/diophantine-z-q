module
public import ActualOriginalCoprimeFourierCount318
public import ActualResidueDigitEquiv318
public section
noncomputable section
namespace ActualOriginalResidueFourierLift318
open QuadricCRTAssembly318 ActualResidueDigitEquiv318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The exact standard character descends after multiplication by p.
The moduli need not be coprime. -/
lemma actual_character_reduce (m p : ℕ) [NeZero m] [NeZero p]
    (z : ZMod (m*p)) :
    ZMod.stdAddChar ((p : ZMod (m*p))*z) = ZMod.stdAddChar (reduce m p z) := by
  have hi (n : ℤ) : ZMod.stdAddChar ((p*n : ℤ) : ZMod (m*p)) =
      ZMod.stdAddChar (n : ZMod m) := by
    rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
    congr 1
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
    push_cast
    field_simp [hp,hm]
    <;> ring
  have hz := hi (z.val : ℤ)
  have hr : reduce m p z = (z.val : ZMod m) := (actual_base_component m p z).symm
  rw [hr]
  simpa only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val] using hz

@[expose] def splitCoordinates (R S : Type*) [CommRing R] [CommRing S] :
    Coordinates (R×S) ≃ Coordinates R × Coordinates S where
  toFun x := (mapCoordinates (RingHom.fst R S) x,mapCoordinates (RingHom.snd R S) x)
  invFun x := ActualOriginalProductQuadric318.mergeCoordinates x.1 x.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The base-m digit equivalence is applied to all FIVE original
coordinates, then regrouped into base coordinates and p-digit coordinates. -/
@[expose] def coordinateDigitEquiv (m p : ℕ) [NeZero m] [NeZero p] :
    Coordinates (ZMod (m*p)) ≃ Coordinates (ZMod m) × Coordinates (ZMod p) :=
  (((digitEquiv m p).prodCongr (digitEquiv m p)).prodCongr
    (((digitEquiv m p).prodCongr (digitEquiv m p)).prodCongr (digitEquiv m p))).trans
      (splitCoordinates (ZMod m) (ZMod p))

lemma coordinateDigitEquiv_base (m p : ℕ) [NeZero m] [NeZero p]
    (x : Coordinates (ZMod (m*p))) :
    (coordinateDigitEquiv m p x).1 = mapCoordinates (reduce m p) x := by
  change (((digitEquiv m p x.1.1).1,(digitEquiv m p x.1.2).1),
    ((digitEquiv m p x.2.1.1).1,(digitEquiv m p x.2.1.2).1),
    (digitEquiv m p x.2.2).1) = _
  simp only [actual_base_component,mapCoordinates]

/-- Every base vector has exactly p^5 genuine residue lifts. -/
theorem actual_five_coordinate_sum (m p : ℕ) [NeZero m] [NeZero p]
    (f : Coordinates (ZMod m) → ℂ) :
    (∑ x : Coordinates (ZMod (m*p)), f (mapCoordinates (reduce m p) x)) =
      (p : ℂ)^5 * ∑ x : Coordinates (ZMod m), f x := by
  classical
  have he := Equiv.sum_comp (coordinateDigitEquiv m p)
    (fun x : Coordinates (ZMod m) × Coordinates (ZMod p) => f x.1)
  simp only [coordinateDigitEquiv_base] at he
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [←Finset.mul_sum]
  simp only [Coordinates,Fintype.card_prod,ZMod.card,Nat.cast_mul]
  ring

/-- The original quadratic phase is reduced through the actual ring
map, retaining the same integer kappa and all five coordinates. -/
lemma actual_scaled_phase (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (a : ZMod m) (x : Coordinates (ZMod (m*p))) :
    ZMod.stdAddChar (((p : ZMod (m*p))*(a.val : ZMod (m*p)))*equation (κ : ZMod (m*p)) x) =
      ZMod.stdAddChar (a*equation (κ : ZMod m) (mapCoordinates (reduce m p) x)) := by
  rw [mul_assoc,actual_character_reduce,map_mul]
  have ha : reduce m p (a.val : ZMod (m*p)) = a := by
    rw [map_natCast,ZMod.natCast_zmod_val]
  rw [ha,←equation_map,map_intCast]

end ActualOriginalResidueFourierLift318
