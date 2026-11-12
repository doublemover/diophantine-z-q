module
public import OriginalThreeDimensionalTransference318
public section
noncomputable section
namespace OriginalThirdMinimumTail318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalDualDenominator318 OriginalThreeDimensionalTransference318
open NonzeroMultipleBox318 TriangularLatticeBoxCount318 OriginalShortDualLattices318
set_option maxHeartbeats 3500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def floorRadius (A : ℝ) : ℕ := ⌊A⌋.toNat
lemma floorRadius_cast (A : ℝ) (hA : 0≤A) : (floorRadius A:ℤ)=⌊A⌋ :=
  Int.toNat_of_nonneg (Int.floor_nonneg.mpr hA)
lemma floorRadius_le (A : ℝ) (hA : 0≤A) : (floorRadius A:ℝ)≤A := by
  have he : (floorRadius A:ℝ)=(⌊A⌋:ℝ) := by exact_mod_cast floorRadius_cast A hA
  rw [he]
  exact Int.floor_le A

lemma integral_coordinate_floor (z : ℤ) (A : ℝ) (hA : 0≤A) (hz : |(z:ℝ)|≤A) :
    |z|≤(floorRadius A:ℤ) := by
  rw [floorRadius_cast A hA]
  apply Int.le_floor.mpr
  simpa only [Int.cast_abs] using hz

@[expose] def Exceptional (p : ι → ℕ) (κ : ℤ) (T : ℝ) :=
  {t : ∀ i, Option (ZMod (p i)) // LargeThird p κ t T}
@[expose] def radius (p : ι → ℕ) (T : ℝ) : ℕ :=
  floorRadius (2*(FixedSquarefreeCRT318.modulus p:ℝ)/T)

/-- The PRODUCED dual vector has an actual original integer numerator.
Each INTEGER coordinate lies in the floor box. We do NOT incorrectly
round the Euclidean norm itself down to that integer radius. -/
theorem exceptional_to_integer (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (T : ℝ) (hT : 0<T) (t : ∀ i, Option (ZMod (p i)))
    (ht : LargeThird p κ t T) :
    ∃ v : NonzeroBox (radius p T), ∀ u : Vector ℤ, u∈literalLattice p κ t →
      (FixedSquarefreeCRT318.modulus p:ℤ)∣dot (coordinates v.1) u := by
  let M := FixedSquarefreeCRT318.modulus p
  let A : ℝ := 2*(M:ℝ)/T
  have hM : (0:ℝ)<M := by exact_mod_cast FixedSquarefreeCRT318.modulus_positive p hp
  have hA : 0≤A := by positivity
  obtain ⟨d,hd,hdne,hdnorm⟩ := large_third_has_short_dual p hp κ t T hT ht
  obtain ⟨v,hv,he⟩ := (actual_dual_iff p hp κ t d).mp hd
  have hvne : v≠0 := by
    intro hz
    apply hdne
    rw [←he,hz,normalized_zero]
  have hscale : (M:ℝ) • d=embed v := by
    rw [←he]
    simp only [normalized,smul_smul,mul_inv_cancel₀ hM.ne',one_smul]
  have hnorm : ‖embed v‖≤A := by
    rw [←hscale,norm_smul,Real.norm_of_nonneg hM.le]
    calc
      (M:ℝ)*‖d‖≤(M:ℝ)*(2/T) := mul_le_mul_of_nonneg_left hdnorm.le hM.le
      _ = A := by dsimp [A]; ring
  have hcoord (i : Fin 3) : |embed v i|≤A := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (embed v) i).trans hnorm
  have hx : |v.1|≤(radius p T:ℤ) := integral_coordinate_floor v.1 A hA (hcoord 0)
  have hz : |v.2.1|≤(radius p T:ℤ) := integral_coordinate_floor v.2.1 A hA (hcoord 1)
  have hw : |v.2.2|≤(radius p T:ℤ) := integral_coordinate_floor v.2.2 A hA (hcoord 2)
  let vb : Box (radius p T) := (⟨v.1,Finset.mem_Icc.mpr (abs_le.mp hx)⟩,
    ⟨v.2.1,Finset.mem_Icc.mpr (abs_le.mp hz)⟩,
    ⟨v.2.2,Finset.mem_Icc.mpr (abs_le.mp hw)⟩)
  refine ⟨⟨vb,?_⟩,?_⟩
  · change v≠0
    exact hvne
  · change ∀ u : Vector ℤ, u∈literalLattice p κ t → (M:ℤ)∣dot v u
    exact hv

/-- Actual original lattice-family count, now consuming the constructed
transference theorem and exact floor-coordinate injection. -/
theorem exceptional_count (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (T : ℝ) (hT : 0<T) :
    Nat.card (Exceptional p κ T)≤27*4^(Fintype.card ι)*(radius p T)^3 := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  let f : Exceptional p κ T → ShortDual p κ (radius p T) := fun t =>
    ⟨t.1,exceptional_to_integer p hp κ T hT t.1 t.2⟩
  have hi : Function.Injective f := by intro s t he; exact Subtype.ext (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective f hi).trans
    (original_short_dual_bound p hp hd κ hκ (radius p T))

/-- Quantitative THIRD-MINIMUM TAIL for the actual original family.
The T^3 denominator is written multiplicatively to retain all exact
constants and avoid a hidden zero/negative-radius convention. -/
theorem actual_third_minimum_tail (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (T : ℝ) (hT : 0<T) :
    (Nat.card (Exceptional p κ T):ℝ)*T^3≤
      216*(4:ℝ)^(Fintype.card ι)*(FixedSquarefreeCRT318.modulus p:ℝ)^3 := by
  let M := FixedSquarefreeCRT318.modulus p
  let B := radius p T
  have hM : (0:ℝ)<M := by exact_mod_cast FixedSquarefreeCRT318.modulus_positive p hp
  have hB : (B:ℝ)≤2*(M:ℝ)/T := floorRadius_le _ (by positivity)
  have hBT : (B:ℝ)*T≤2*(M:ℝ) := (le_div_iff₀ hT).mp hB
  have hcube := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg B) hT.le) hBT 3
  have hcount : (Nat.card (Exceptional p κ T):ℝ)≤27*(4:ℝ)^(Fintype.card ι)*(B:ℝ)^3 := by
    exact_mod_cast exceptional_count p hp hd κ hκ T hT
  calc
    _ ≤ (27*(4:ℝ)^(Fintype.card ι)*(B:ℝ)^3)*T^3 :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hT.le 3)
    _ = (27*(4:ℝ)^(Fintype.card ι))*((B:ℝ)*T)^3 := by ring
    _ ≤ (27*(4:ℝ)^(Fintype.card ι))*(2*(M:ℝ))^3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 216*(4:ℝ)^(Fintype.card ι)*(M:ℝ)^3 := by ring

/-- Instantiate the tail on the manuscript's ACTUAL retained prime
factors of the original slice label, outside2κ. No supplied modulus,
prime list, lattice index, minimum or transference input remains. -/
theorem actual_slice_tail (κ label : ℤ) (T : ℝ) (hT : 0<T) :
    (Nat.card (Exceptional (LiteralSliceModulus318.prime κ label) κ T):ℝ)*T^3≤
      216*(4:ℝ)^(LiteralSliceModulus318.retained κ label).card*
        (LiteralSliceModulus318.modulus κ label:ℝ)^3 := by
  classical
  simpa only [LiteralSliceModulus318.PrimeIndex,Fintype.card_coe,LiteralSliceModulus318.modulus] using
    actual_third_minimum_tail (LiteralSliceModulus318.prime κ label)
      (LiteralSliceModulus318.prime_is_prime κ label) (LiteralSliceModulus318.prime_injective κ label)
      κ (LiteralSliceModulus318.prime_avoids_coefficient κ label) T hT

end OriginalThirdMinimumTail318
