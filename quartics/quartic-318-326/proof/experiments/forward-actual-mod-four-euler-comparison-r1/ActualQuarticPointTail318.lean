module
public import ActualQuarticOffsetZeroLocus318
public section
noncomputable section
namespace ActualQuarticPointTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalNormPointSieveTail318
open OriginalAffineSieveEliminants318 OriginalAffinePrimeSupport318
open OriginalQuadraticIntegerFibers318 IntegerResidueBoxCount318
open ActualGaussianChartObstruction318 ActualAffineQuarticEliminant318 OriginalLargePrimeDivisorCount318
set_option maxHeartbeats 6500000

/-- Actual original integer points on ONE affine fiber. Only the leading
condition is filtered here; the bounded-shear cover supplies it per prime. -/
@[expose] def FiberBad (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ) :=
  {h : Interval B // ∃ p : ℕ, p.Prime ∧ Y<p ∧ 2*B<p ∧
    ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p}

lemma single_prime_count (κ t : ℤ) (a d : Vector ℤ) (B p : ℕ) :
    Nat.card {h : Interval B // p.Prime ∧ 2*B<p ∧
      ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p}≤2 := by
  classical
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    by_cases hlarge : 2*B<p
    · by_cases ha : ¬(p:ℤ)∣fA true κ t d
      · let f : {h : Interval B // p.Prime ∧ 2*B<p ∧
            ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p} →
          IntegerRoots B p (fA true κ t d) (fB true κ t a d) (fC true κ t a) :=
          fun h => ⟨h.1,by
            have hh := h.2.2.2.2.1
            rw [actual_affine_polynomial] at hh
            exact hh⟩
        have hf : Function.Injective f := fun h k he => Subtype.ext (congrArg Subtype.val he)
        exact (Nat.card_le_card_of_injective f hf).trans (large_prime_root_count B p _ _ _ ha hlarge)
      · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
            ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p} :=
          ⟨fun h => ha h.2.2.2.1⟩
        simp
    · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
          ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p} :=
        ⟨fun h => hlarge h.2.2.1⟩
      simp
  · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
        ¬(p:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p} :=
      ⟨fun h => hp h.2.1⟩
    simp

/-- Overlap-safe actual point count, from a PRODUCED finite prime cover.
The cover is instantiated below with the original eliminants. -/
theorem finite_support_points (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ)
    (S : Finset ℕ)
    (hcover : ∀ h : Interval B, ∀ p : ℕ, p.Prime → Y<p → 2*B<p →
      ¬(p:ℤ)∣fA true κ t d → Obstruction true κ t (affine a d h.1) p → p∈S) :
    Nat.card (FiberBad κ t a d B Y)≤2*S.card := by
  classical
  let P : ↥S → Interval B → Prop := fun p h => p.1.Prime ∧ 2*B<p.1 ∧
    ¬(p.1:ℤ)∣fA true κ t d ∧ Obstruction true κ t (affine a d h.1) p.1
  let f : FiberBad κ t a d B Y → {h : Interval B // ∃ p : ↥S, P p h} := fun h =>
    ⟨h.1,by
      obtain ⟨p,hp,hY,hB,hA,ho⟩ := h.2
      exact ⟨⟨p,hcover h.1 p hp hY hB hA ho⟩,hp,hB,hA,ho⟩⟩
  have hf : Function.Injective f := fun h k he => Subtype.ext (congrArg Subtype.val he)
  have hunion := OriginalFiniteSieveUnion318.finite_union_card P
  have hs : (∑ p : ↥S, Nat.card {h : Interval B // P p h})≤2*S.card := by
    calc
      _ ≤ ∑ _p : ↥S, 2 := Finset.sum_le_sum (fun p _ => single_prime_count κ t a d B p.1)
      _ = _ := by simp [Nat.mul_comm]
  exact (Nat.card_le_card_of_injective f hf).trans (hunion.trans hs)


/-- Actual point count on a nonzero true-quartic eliminant fiber. Its
finite prime support is constructed from that exact integer, with no
leading-prime omission in the eliminant identity. -/
theorem actual_fiber_tail (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ)
    (hY : 1<Y) (hE : actualEliminant κ t a d≠0)
    (N : ℝ) (hN : |(actualEliminant κ t a d:ℝ)|≤N) :
    (Nat.card (FiberBad κ t a d B Y):ℝ)*Real.log (Y:ℝ)≤2*Real.log N := by
  have hc := finite_support_points κ t a d B Y (largeDivisors (actualEliminant κ t a d) Y)
    (fun h p hp hYp _ _ ho => (mem_largeDivisors _ hE Y p).mpr
      ⟨hp,actual_obstruction_eliminates κ t a d h.1 p ho,hYp⟩)
  have hl := actual_large_divisor_height (actualEliminant κ t a d) hE Y hY N hN
  have hlog : 0≤Real.log (Y:ℝ) := (Real.log_pos (by exact_mod_cast hY)).le
  have hcR : (Nat.card (FiberBad κ t a d B Y):ℝ)≤
      2*((largeDivisors (actualEliminant κ t a d) Y).card:ℝ) := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hcR hlog]

end ActualQuarticPointTail318
