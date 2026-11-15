module
public import ActualAmbientQuadricLift318
public section
noncomputable section
namespace ActualPrimitiveResidueLiftSet318
open scoped BigOperators
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualAmbientQuadricLift318
set_option maxHeartbeats 24000000

@[expose] def reduceQuadric (κ : ℤ) (m p : ℕ) (y : Quadric (κ:ZMod (m*p))) :
    Quadric (κ:ZMod m) :=
  ⟨mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y.1,by
    rw [←map_intCast (ActualResidueDigitEquiv318.reduce m p) κ,equation_map,y.2,map_zero]⟩
@[expose] def LiftSet (κ : ℤ) (m p : ℕ) (R : Finset (Quadric (κ:ZMod m))) :=
  {y : Quadric (κ:ZMod (m*p)) // reduceQuadric κ m p y∈R}

/-- Every actual ambient lift belongs to exactly its original base
class. This includes arbitrary prescribed local subsets, not only the
full smooth residue locus or one independently chosen class. -/
@[expose] def preimageEquiv (κ : ℤ) (m p : ℕ) (R : Finset (Quadric (κ:ZMod m))) :
    LiftSet κ m p R ≃ (Σx : ↥R,QuadricFiber κ m p x.1) where
  toFun y := ⟨⟨reduceQuadric κ m p y.1,y.2⟩,⟨y.1,rfl⟩⟩
  invFun z := ⟨z.2.1,by
    have he : reduceQuadric κ m p z.2.1=z.1.1 := Subtype.ext z.2.2
    rw [he]
    exact z.1.2⟩
  left_inv y := rfl
  right_inv z := by
    rcases z with ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have he : reduceQuadric κ m p y=x := Subtype.ext hy
    subst x
    rfl

/-- The full original ambient residue preimage has p^4 times the
cardinality of ANY prescribed primitive base subset, including empty. -/
theorem actual_primitive_subset_lift_count (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m)
    (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)≠((0,0),(0,0),0)) :
    Nat.card (LiftSet κ m p R)=R.card*p^4 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype (LiftSet κ m p R) := Fintype.ofFinite _
  letI : ∀x : ↥R,Fintype (QuadricFiber κ m p x.1) := fun _ => Fintype.ofFinite _
  rw [Nat.card_congr (preimageEquiv κ m p R),Nat.card_eq_fintype_card,Fintype.card_sigma]
  calc
    _ = ∑x : ↥R,p^4 := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Nat.card_eq_fintype_card] using
        actual_ambient_quadric_lift_count κ m p hp hp2 hκ hpm x.1 (hR x.1 x.2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]

lemma scalar_prime_reduction (m p : ℕ) [NeZero m] [NeZero p] (hpm : p∣m)
    (y : ZMod (m*p)) : ((ActualResidueDigitEquiv318.reduce m p y).val:ZMod p)=(y.val:ZMod p) := by
  let f : ZMod m →+* ZMod p := ZMod.castHom hpm (ZMod p)
  calc
    _ = f ((ActualResidueDigitEquiv318.reduce m p y).val:ZMod m) := (map_natCast f _).symm
    _ = f (ActualResidueDigitEquiv318.reduce m p y) := by rw [ZMod.natCast_zmod_val]
    _ = f (y.val:ZMod m) := congrArg f (ActualResidueDigitEquiv318.actual_base_component m p y).symm
    _ = _ := map_natCast f _

lemma actual_reduction_compatibility (m p : ℕ) [NeZero m] [NeZero p] (hpm : p∣m)
    (y : Coordinates (ZMod (m*p))) :
    mapCoordinates (Int.castRingHom (ZMod p))
      (digits m (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y))=
      mapCoordinates (Int.castRingHom (ZMod p)) (digits (m*p) y) := by
  simp only [mapCoordinates,digits,Int.castRingHom_apply,Int.cast_natCast]
  exact Prod.ext
    (Prod.ext (scalar_prime_reduction m p hpm y.1.1) (scalar_prime_reduction m p hpm y.1.2))
    (Prod.ext
      (Prod.ext (scalar_prime_reduction m p hpm y.2.1.1) (scalar_prime_reduction m p hpm y.2.1.2))
      (scalar_prime_reduction m p hpm y.2.2))

/-- Every one of the counted ambient lifts remains primitive at the
ORIGINAL prime. This is needed before iterating the p^4 recurrence. -/
theorem actual_lift_preserves_primitivity (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hpm : p∣m) (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)≠((0,0),(0,0),0))
    (y : LiftSet κ m p R) :
    mapCoordinates (Int.castRingHom (ZMod p)) (digits (m*p) y.1.1)≠((0,0),(0,0),0) := by
  have hh := hR (reduceQuadric κ m p y.1) y.2
  change mapCoordinates (Int.castRingHom (ZMod p))
    (digits m (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y.1.1))≠_ at hh
  rw [actual_reduction_compatibility m p hpm] at hh
  exact hh

end ActualPrimitiveResidueLiftSet318
