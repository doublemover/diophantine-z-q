module
public import ActualQuarticPointTail318
public section
noncomputable section
namespace ActualQuarticRectangleTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 IntegerResidueBoxCount318
open OriginalOffsetEliminant318 OriginalOffsetZeroLocus318 OriginalBoundedIntegerShear318
open OriginalControlledIntegralBasis318 ActualAffineQuarticEliminant318
open ActualQuarticPointTail318 ActualQuarticOffsetZeroLocus318 ActualOriginalEliminantNonzero318
open OriginalAffineRectangleTail318 (sum_with_bad_fibers)
set_option maxHeartbeats 8500000

@[expose] def RectangleBad (κ t : ℤ) (u v d : Vector ℤ) (A B C Y : ℕ) :=
  Σ a : Interval A×Interval B, FiberBad κ t (offset u v a.1.1 a.2.1) d C Y

/-- A uniform height is CONSTRUCTED from actual integer eliminants on
the finite offset rectangle. Polynomial-size optimization remains a
separate step; no unexplained caller-supplied height enters this endpoint. -/
@[expose] def rectangleHeight (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) : ℝ :=
  1+∑ a : Interval A×Interval B, |(actualEliminant κ t (offset u v a.1.1 a.2.1) d:ℝ)|
lemma height_one (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) : 1≤rectangleHeight κ t u v d A B := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
lemma actual_height (κ t : ℤ) (u v d : Vector ℤ) (A B : ℕ) (a : Interval A×Interval B) :
    |(actualEliminant κ t (offset u v a.1.1 a.2.1) d:ℝ)|≤rectangleHeight κ t u v d A B := by
  have hh := Finset.single_le_sum (fun b (_ : b∈Finset.univ) =>
    abs_nonneg (actualEliminant κ t (offset u v b.1.1 b.2.1) d:ℝ)) (Finset.mem_univ a)
  exact hh.trans (le_add_of_nonneg_left (by norm_num))

lemma fiber_trivial (κ t : ℤ) (a d : Vector ℤ) (C Y : ℕ) :
    Nat.card (FiberBad κ t a d C Y)≤2*C+1 := by
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : FiberBad κ t a d C Y → Interval C) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card,Interval,Fintype.card_coe,interval_card] using hh

/-- The TRUE quartic rectangle bound counts every exceptional zero
cylinder, including t=-2, rather than incorrectly claiming those fibers
are all nonzero. Both support and height are constructed at actual points. -/
theorem rectangle_tail (κ t : ℤ) (u v d : Vector ℤ) (A B C Y : ℕ) (hY : 1<Y)
    (hn : ActualQuarticOffsetPolynomial318.polynomial κ t u v d≠0) :
    (Nat.card (RectangleBad κ t u v d A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*2*Real.log (rectangleHeight κ t u v d A B)+
        8*((2*A+1:ℕ)+(2*B+1):ℝ)*(2*C+1)*Real.log (Y:ℝ) := by
  classical
  let bad : Interval A×Interval B → Prop := fun a => actualEliminant κ t (offset u v a.1.1 a.2.1) d=0
  let n : Interval A×Interval B → ℕ := fun a => Nat.card (FiberBad κ t (offset u v a.1.1 a.2.1) d C Y)
  let N := rectangleHeight κ t u v d A B
  have hl : 0≤Real.log (Y:ℝ) := (Real.log_pos (by exact_mod_cast hY)).le
  have hlN : 0≤Real.log N := Real.log_nonneg (height_one κ t u v d A B)
  have hh := sum_with_bad_fibers n bad (Real.log (Y:ℝ)) (2*Real.log N)
    ((2*C+1)*Real.log (Y:ℝ)) hl (by positivity) (by positivity) (by
      intro a ha
      exact actual_fiber_tail κ t _ d C Y hY ha N (actual_height κ t u v d A B a)) (by
      intro a ha
      have hb : (n a:ℝ)≤2*C+1 := by exact_mod_cast fiber_trivial κ t _ d C Y
      exact mul_le_mul_of_nonneg_right hb hl)
  have hzero : (Nat.card {a : Interval A×Interval B // bad a}:ℝ)≤
      8*((2*A+1:ℕ)+(2*B+1):ℝ) := by exact_mod_cast zero_count κ t u v d A B hn
  have hcard : (Nat.card (RectangleBad κ t u v d A B C Y):ℝ)=∑ a, (n a:ℝ) := by
    simp only [RectangleBad,Nat.card_eq_fintype_card,Fintype.card_sigma,n,Nat.cast_sum]
  have hall : Fintype.card (Interval A×Interval B)=(2*A+1)*(2*B+1) := by
    simp only [Fintype.card_prod,Interval,Fintype.card_coe,interval_card]
  rw [hcard]
  rw [hall] at hh
  have hmul := mul_le_mul_of_nonneg_right hzero (show 0≤(2*C+1:ℝ)*Real.log (Y:ℝ) by positivity)
  push_cast at hh hmul ⊢
  nlinarith only [hh,hmul]

/-- Original whole basis and actual leading shear produce every
nonvanishing input internally, at the unchanged source label and index. -/
theorem actual_original_rectangle (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (i j : ℤ) (hA : OriginalAffineSieveEliminants318.fA true κ t (shear i j u v z)≠0)
    (A B C Y : ℕ) (hY : 1<Y) :
    (Nat.card (RectangleBad κ t u v (shear i j u v z) A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*2*Real.log (rectangleHeight κ t u v (shear i j u v z) A B)+
        8*((2*A+1:ℕ)+(2*B+1):ℝ)*(2*C+1)*Real.log (Y:ℝ) :=
  rectangle_tail κ t u v _ A B C Y hY (actual_original_shear κ t hκ ht s u v z hb i j hA)

end ActualQuarticRectangleTail318
