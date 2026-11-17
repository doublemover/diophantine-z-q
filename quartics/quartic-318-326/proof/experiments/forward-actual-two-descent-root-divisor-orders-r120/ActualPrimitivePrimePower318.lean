module
public import ActualPrimitiveResidueLiftSet318
public section
noncomputable section
namespace ActualPrimitivePrimePower318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualPrimitiveResidueLiftSet318
set_option maxHeartbeats 24000000

/-- Primitivity is at the ORIGINAL prime, not merely nonzero modulo m. -/
@[expose] def IsPrimitive (κ : ℤ) (m p : ℕ) (x : Quadric (κ:ZMod m)) : Prop :=
  mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1)≠((0,0),(0,0),0)
@[expose] def PrimitiveResidues (κ : ℤ) (m p : ℕ) :=
  {x : Quadric (κ:ZMod m) // IsPrimitive κ m p x}
@[expose] def primitiveSet (κ : ℤ) (m p : ℕ) [NeZero m] : Finset (Quadric (κ:ZMod m)) := by
  classical
  exact Finset.univ.filter (IsPrimitive κ m p)
lemma mem_primitiveSet (κ : ℤ) (m p : ℕ) [NeZero m] (x : Quadric (κ:ZMod m)) :
    x∈primitiveSet κ m p ↔ IsPrimitive κ m p x := by
  classical
  simp only [primitiveSet,Finset.mem_filter,Finset.mem_univ,true_and]
lemma primitiveSet_card (κ : ℤ) (m p : ℕ) [NeZero m] :
    (primitiveSet κ m p).card=Nat.card (PrimitiveResidues κ m p) := by
  classical
  unfold primitiveSet PrimitiveResidues
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- All primitive residues at the next modulus are exactly the full
ambient preimage of the original primitive locus. -/
@[expose] def primitivePreimageEquiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hpm : p∣m) : PrimitiveResidues κ (m*p) p ≃ LiftSet κ m p (primitiveSet κ m p) where
  toFun y := ⟨y.1,by
    apply (mem_primitiveSet κ m p _).mpr
    change mapCoordinates (Int.castRingHom (ZMod p))
      (digits m (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y.1.1))≠_
    rw [actual_reduction_compatibility m p hpm]
    exact y.2⟩
  invFun y := ⟨y.1,actual_lift_preserves_primitivity κ m p hpm _
    (fun x hx => (mem_primitiveSet κ m p x).mp hx) y⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_primitive_count_step (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m) :
    Nat.card (PrimitiveResidues κ (m*p) p)=Nat.card (PrimitiveResidues κ m p)*p^4 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (primitivePreimageEquiv κ m p hpm),
    actual_primitive_subset_lift_count κ m p hp hp2 hκ hpm _
      (fun x hx => (mem_primitiveSet κ m p x).mp hx),primitiveSet_card]

@[expose] def primeBaseEquiv (κ : ℤ) (p : ℕ) [NeZero p] :
    PrimitiveResidues κ p p ≃
      {x : Quadric (κ:ZMod p) // x≠PrimitiveSieveCRT318.origin (κ:ZMod p)} where
  toFun x := ⟨x.1,by
    intro he
    apply x.2
    rw [digits_reduce,he]
    rfl⟩
  invFun x := ⟨x.1,by
    change mapCoordinates (Int.castRingHom (ZMod p)) (digits p x.1.1)≠_
    rw [digits_reduce]
    intro he
    exact x.2 (Subtype.ext he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_primitive_prime_count (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) :
    Nat.card (PrimitiveResidues κ p p)=p^4-1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_congr (primeBaseEquiv κ p),
    Nat.card_congr (PrimitiveSieveCRT318.nonzeroFieldEquiv (κ:ZMod p))]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  simpa only [ZMod.card] using FiniteFiveQuadricCount318.nonzero_quadric_card hF
    (GoodReductionResidue318.two_residue_ne p hp2) (κ:ZMod p) hk

/-- Exact count of the original primitive locus at EVERY prime power.
The exponent is written e+1 so there is no truncated subtraction case. -/
theorem actual_primitive_prime_power_count (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    Nat.card (PrimitiveResidues κ (p^(e+1)) p)=(p^4-1)*(p^4)^e := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  induction e with
  | zero => simpa only [zero_add,pow_one,pow_zero,mul_one] using
      actual_primitive_prime_count κ p hp hp2 hκ
  | succ e ih =>
    have hd : p∣p^(e+1) := dvd_pow_self _ (by omega)
    have hh := actual_primitive_count_step κ (p^(e+1)) p hp hp2 hκ hd
    rw [←pow_succ] at hh
    rw [hh,ih,pow_succ (p^4) e]
    exact mul_assoc _ _ _

end ActualPrimitivePrimePower318
