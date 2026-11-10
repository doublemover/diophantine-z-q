module
public import OriginalBadLatticePointTail318
public section
noncomputable section
namespace OriginalBadSlicePointTail318
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceModulus318 LiteralSliceBoxCount318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 TriangularLatticeBoxCount318
open OriginalThreeDimensionalTransference318 OriginalBadLatticePointTail318
set_option maxHeartbeats 3000000

/-- Actual bounded ORIGINAL five-coordinate slice points whose projected
original ternary point lies in an exceptional original lattice. -/
@[expose] def BadSlice (B : ℕ) (κ label : ℤ) (side : Bool) (T : ℝ) :=
  {v : BoundedSlice B κ label side // ∃ s : ∀ i : PrimeIndex κ label, Option (ZMod (prime κ label i)),
    LargeThird (prime κ label) κ s T ∧ project v.1.1.1∈literalLattice (prime κ label) κ s}

@[expose] def badSliceEncode (B : ℕ) (κ label : ℤ) (side : Bool) (T : ℝ) :
    BadSlice B κ label side T → BadPoints (2*B) (prime κ label) κ T := fun v =>
  ⟨projectedBox B κ label side v.1,by
    obtain ⟨s,hs,hmem⟩ := v.2
    exact ⟨s,hs,hmem⟩⟩

lemma badSliceEncode_injective (B : ℕ) (κ label : ℤ) (hlabel : label≠0) (side : Bool) (T : ℝ) :
    Function.Injective (badSliceEncode B κ label side T) := by
  intro v w he
  apply Subtype.ext
  apply LiteralSliceBoxCount318.encode_injective B κ label hlabel side
  apply Subtype.ext
  exact congrArg Subtype.val he

/-- The actual original fixed-label bad-point contribution. The doubled
coordinate box costs exactly8; the original fixed-slice map is injective,
not claimed unimodular, and parity is only discarded through that injection. -/
theorem actual_bad_slice_tail (B : ℕ) (κ label : ℤ) (hlabel : label≠0)
    (hlabelB : label.natAbs≤2*B) (side : Bool) (T : ℝ) (hT : 0<T) :
    (Nat.card (BadSlice B κ label side T):ℝ)*T^3≤
      46656*(4:ℝ)^(retained κ label).card*(modulus κ label:ℝ)*(B:ℝ)^3 := by
  classical
  have hM : modulus κ label≤2*B := (modulus_le_label κ label hlabel).trans hlabelB
  have hc := Nat.card_le_card_of_injective (badSliceEncode B κ label side T)
    (badSliceEncode_injective B κ label hlabel side T)
  have hcr : (Nat.card (BadSlice B κ label side T):ℝ)≤
      (Nat.card (BadPoints (2*B) (prime κ label) κ T):ℝ) := by exact_mod_cast hc
  have hb := actual_bad_point_tail (2*B) (prime κ label) (prime_is_prime κ label)
    (prime_injective κ label) (prime_odd κ label) κ (prime_avoids_coefficient κ label) T hT hM
  have hh := (mul_le_mul_of_nonneg_right hcr (pow_nonneg hT.le 3)).trans hb
  simpa only [PrimeIndex,Fintype.card_coe,modulus,Nat.cast_mul,Nat.cast_ofNat,mul_pow] using
    (show (Nat.card (BadSlice B κ label side T):ℝ)*T^3≤
      46656*(4:ℝ)^(Fintype.card (PrimeIndex κ label))*(modulus κ label:ℝ)*(B:ℝ)^3 by
      convert hh using 1 <;> push_cast <;> ring)

end OriginalBadSlicePointTail318
