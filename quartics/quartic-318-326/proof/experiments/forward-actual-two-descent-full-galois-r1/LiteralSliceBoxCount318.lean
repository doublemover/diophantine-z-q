module
public import LiteralSliceModulus318
public section
noncomputable section
namespace LiteralSliceBoxCount318
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceModulus318
open IntegerResidueBoxCount318 TriangularLatticeBoxCount318
set_option maxHeartbeats 1000000

@[expose] def InBox (B : ℕ) (v : Coordinates ℤ) : Prop :=
  (-(B:ℤ)≤v.1.1 ∧ v.1.1≤B) ∧ (-(B:ℤ)≤v.1.2 ∧ v.1.2≤B) ∧
  (-(B:ℤ)≤v.2.1.1 ∧ v.2.1.1≤B) ∧ (-(B:ℤ)≤v.2.1.2 ∧ v.2.1.2≤B) ∧
  (-(B:ℤ)≤v.2.2 ∧ v.2.2≤B)
@[expose] def BoundedSlice (B : ℕ) (κ t : ℤ) (side : Bool) :=
  {v : Slice κ t side // InBox B v.1.1}

/-- Actual integer projection into the doubled-radius box, not a replacement
by a freely supplied ternary point. -/
@[expose] def projectedBox (B : ℕ) (κ t : ℤ) (side : Bool)
    (v : BoundedSlice B κ t side) : Box (2*B) := by
  obtain ⟨ha,hb,hc,hd,hw⟩ := v.2
  refine (⟨v.1.1.1.1.2-v.1.1.1.2.1.2,?_⟩,
    ⟨v.1.1.1.1.2+v.1.1.1.2.1.2,?_⟩,⟨v.1.1.1.2.2,?_⟩)
  all_goals apply Finset.mem_Icc.mpr; push_cast; constructor <;> omega

lemma projected_coordinates (B : ℕ) (κ t : ℤ) (side : Bool)
    (v : BoundedSlice B κ t side) :
    coordinates (projectedBox B κ t side v)=project v.1.1.1 := rfl

@[expose] def encode (B : ℕ) (κ t : ℤ) (side : Bool) :
    BoundedSlice B κ t side → LiteralTernaryReduction318.LiteralBox (2*B) (prime κ t) κ :=
  fun v => ⟨projectedBox B κ t side v,by
    rw [projected_coordinates]
    exact slice_modulus_divides κ t side v.1 (modulus κ t) (modulus_divides_label κ t)⟩

lemma encode_injective (B : ℕ) (κ t : ℤ) (ht : t≠0) (side : Bool) :
    Function.Injective (encode B κ t side) := by
  intro v u he
  apply Subtype.ext
  apply slice_projection_injective κ t ht side
  have h := congrArg (fun z : LiteralTernaryReduction318.LiteralBox (2*B) (prime κ t) κ =>
    coordinates z.1) he
  exact h

/-- Exact original five-coordinate slice count, with q constructed from the
actual slice label and all source parity restrictions retained before the
injective upper bound. No uniform lattice-counting input is supplied. -/
theorem original_slice_scaled (B : ℕ) (κ t : ℤ) (ht : t≠0)
    (htB : t.natAbs≤2*B) (side : Bool) :
    Nat.card (BoundedSlice B κ t side)*modulus κ t≤
      216*2^(Fintype.card (PrimeIndex κ t))*B^3 := by
  classical
  have hM : modulus κ t≤2*B := (modulus_le_label κ t ht).trans htB
  letI : Finite (BoundedSlice B κ t side) :=
    Finite.of_injective (encode B κ t side) (encode_injective B κ t ht side)
  have hc := Nat.card_le_card_of_injective (encode B κ t side) (encode_injective B κ t ht side)
  have hb := LiteralTernaryReduction318.literal_box_scaled (2*B)
    (prime κ t) (prime_is_prime κ t) (prime_injective κ t) (prime_odd κ t)
    κ (prime_avoids_coefficient κ t) hM
  have hh := (Nat.mul_le_mul_right (modulus κ t) hc).trans hb
  convert hh using 1 <;> ring

end LiteralSliceBoxCount318
