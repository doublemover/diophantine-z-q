module
public import ActualOddBadPrimeObstruction318
public section
noncomputable section
namespace ActualOddRegularResidueTower318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualPrimitiveResidueLiftSet318
open ActualOddRegularLift318 ActualOddBadPrimeObstruction318 ActualPrimitivePrimePower318
set_option maxHeartbeats 28000000

@[expose] def IsRegular (κ : ℤ) (m p : ℕ) (x : Quadric (κ:ZMod m)) : Prop :=
  Regular (mapCoordinates (Int.castRingHom (ZMod p)) (digits m x.1))
@[expose] def RegularResidues (κ : ℤ) (m p : ℕ) :=
  {x : Quadric (κ:ZMod m) // IsRegular κ m p x}
@[expose] def regularSet (κ : ℤ) (m p : ℕ) [NeZero m] : Finset (Quadric (κ:ZMod m)) := by
  classical
  exact Finset.univ.filter (IsRegular κ m p)
lemma mem_regularSet (κ : ℤ) (m p : ℕ) [NeZero m] (x : Quadric (κ:ZMod m)) :
    x∈regularSet κ m p ↔ IsRegular κ m p x := by
  classical
  simp only [regularSet,Finset.mem_filter,Finset.mem_univ,true_and]
lemma regularSet_card (κ : ℤ) (m p : ℕ) [NeZero m] :
    (regularSet κ m p).card=Nat.card (RegularResidues κ m p) := by
  classical
  unfold regularSet RegularResidues
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma actual_regular_reduction (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] (hpm : p∣m)
    (y : Quadric (κ:ZMod (m*p))) :
    IsRegular κ m p (reduceQuadric κ m p y) ↔ IsRegular κ (m*p) p y := by
  unfold IsRegular reduceQuadric
  rw [actual_reduction_compatibility m p hpm]

@[expose] def regularPreimageEquiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hpm : p∣m) : RegularResidues κ (m*p) p ≃ LiftSet κ m p (regularSet κ m p) where
  toFun y := ⟨y.1,(mem_regularSet κ m p _).mpr ((actual_regular_reduction κ m p hpm y.1).mpr y.2)⟩
  invFun y := ⟨y.1,(actual_regular_reduction κ m p hpm y.1).mp ((mem_regularSet κ m p _).mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All regular original classes have their p^4 genuine lifts even
when the original kappa is divisible by the odd prime. -/
theorem actual_regular_subset_count (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hpm : p∣m) (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,IsRegular κ m p x) : Nat.card (LiftSet κ m p R)=R.card*p^4 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype (LiftSet κ m p R) := Fintype.ofFinite _
  letI : ∀x : ↥R,Fintype (ActualAmbientQuadricLift318.QuadricFiber κ m p x.1) :=
    fun _ => Fintype.ofFinite _
  rw [Nat.card_congr (preimageEquiv κ m p R),Nat.card_eq_fintype_card,Fintype.card_sigma]
  calc
    _ = ∑x : ↥R,p^4 := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Nat.card_eq_fintype_card] using
        actual_regular_ambient_count κ m p hp hp2 hpm x.1 (hR x.1 x.2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]

theorem actual_regular_count_step (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hp2 : p≠2) (hpm : p∣m) :
    Nat.card (RegularResidues κ (m*p) p)=Nat.card (RegularResidues κ m p)*p^4 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (regularPreimageEquiv κ m p hpm),
    actual_regular_subset_count κ m p hp hp2 hpm _
      (fun x hx => (mem_regularSet κ m p x).mp hx),regularSet_card]

theorem actual_regular_prime_power_count (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (e : ℕ) :
    Nat.card (RegularResidues κ (p^(e+1)) p)=Nat.card (RegularResidues κ p p)*(p^4)^e := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  induction e with
  | zero => simp only [zero_add,pow_one,pow_zero,mul_one]
  | succ e ih =>
    have hh := actual_regular_count_step κ (p^(e+1)) p hp hp2
      (dvd_pow_self _ (by omega))
    rw [←pow_succ] at hh
    rw [hh,ih,pow_succ (p^4) e]
    exact mul_assoc _ _ _

/-- Above exponent1, the valuation-one obstruction makes the ENTIRE
primitive original source identical to the regular lifting tower. -/
@[expose] def actual_primitive_regular_equiv (κ : ℤ) (m p : ℕ) [NeZero m]
    (hp : p.Prime) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (hpm : p^2∣m) :
    PrimitiveResidues κ m p ≃ RegularResidues κ m p where
  toFun x := ⟨x.1,actual_primitive_is_regular κ m p hp hκ hκ2 hpm x.1 x.2⟩
  invFun x := ⟨x.1,by
    intro he
    apply x.2
    exact congrArg (fun z : Coordinates (ZMod p) => (z.1,z.2.1)) he⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_bad_primitive_count_from_base (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (e : ℕ) :
    Nat.card (PrimitiveResidues κ (p^(e+2)) p)=Nat.card (RegularResidues κ p p)*(p^4)^(e+1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hd : p^2∣p^(e+2) := by
    refine ⟨p^e,?_⟩
    rw [pow_add]
    ring
  rw [Nat.card_congr (actual_primitive_regular_equiv κ (p^(e+2)) p hp hκ hκ2 hd)]
  exact actual_regular_prime_power_count κ p hp hp2 (e+1)

end ActualOddRegularResidueTower318
