module
public import OriginalBoundedIntegerShear318
public section
noncomputable section
namespace OriginalAffinePointTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalNormPointSieveTail318
open OriginalAffineSieveEliminants318 OriginalAffinePrimeSupport318
open OriginalQuadraticIntegerFibers318 IntegerResidueBoxCount318
set_option maxHeartbeats 6500000

/-- Actual original integer points on ONE affine fiber. Only the leading
condition is filtered here; the bounded-shear cover supplies it per prime. -/
@[expose] def FiberBad (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ) :=
  {h : Interval B // ∃ p : ℕ, p.Prime ∧ Y<p ∧ 2*B<p ∧
    ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p}

lemma single_prime_count (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (B p : ℕ) :
    Nat.card {h : Interval B // p.Prime ∧ 2*B<p ∧
      ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p}≤2 := by
  classical
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    by_cases hlarge : 2*B<p
    · by_cases ha : ¬(p:ℤ)∣fA side κ t d
      · let f : {h : Interval B // p.Prime ∧ 2*B<p ∧
            ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p} →
          IntegerRoots B p (fA side κ t d) (fB side κ t a d) (fC side κ t a) :=
          fun h => ⟨h.1,by
            have hh := h.2.2.2.2.1
            rw [actual_affine_polynomial] at hh
            exact hh⟩
        have hf : Function.Injective f := fun h k he => Subtype.ext (congrArg Subtype.val he)
        exact (Nat.card_le_card_of_injective f hf).trans (large_prime_root_count B p _ _ _ ha hlarge)
      · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
            ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p} :=
          ⟨fun h => ha h.2.2.2.1⟩
        simp
    · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
          ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p} :=
        ⟨fun h => hlarge h.2.2.1⟩
      simp
  · haveI : IsEmpty {h : Interval B // p.Prime ∧ 2*B<p ∧
        ¬(p:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p} :=
      ⟨fun h => hp h.2.1⟩
    simp

/-- Overlap-safe actual point count, from a PRODUCED finite prime cover.
The cover is instantiated below with the original eliminants. -/
theorem finite_support_points (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ)
    (S : Finset ℕ)
    (hcover : ∀ h : Interval B, ∀ p : ℕ, p.Prime → Y<p → 2*B<p →
      ¬(p:ℤ)∣fA side κ t d → pointObstruction side κ t (affine a d h.1) p → p∈S) :
    Nat.card (FiberBad side κ t a d B Y)≤2*S.card := by
  classical
  let P : ↥S → Interval B → Prop := fun p h => p.1.Prime ∧ 2*B<p.1 ∧
    ¬(p.1:ℤ)∣fA side κ t d ∧ pointObstruction side κ t (affine a d h.1) p.1
  let f : FiberBad side κ t a d B Y → {h : Interval B // ∃ p : ↥S, P p h} := fun h =>
    ⟨h.1,by
      obtain ⟨p,hp,hY,hB,hA,ho⟩ := h.2
      exact ⟨⟨p,hcover h.1 p hp hY hB hA ho⟩,hp,hB,hA,ho⟩⟩
  have hf : Function.Injective f := fun h k he => Subtype.ext (congrArg Subtype.val he)
  have hunion := OriginalFiniteSieveUnion318.finite_union_card P
  have hs : (∑ p : ↥S, Nat.card {h : Interval B // P p h})≤2*S.card := by
    calc
      _ ≤ ∑ _p : ↥S, 2 := Finset.sum_le_sum (fun p _ => single_prime_count side κ t a d B p.1)
      _ = _ := by simp [Nat.mul_comm]
  exact (Nat.card_le_card_of_injective f hf).trans (hunion.trans hs)

/-- The first actual LARGE-PRIME POINT estimate, not merely a prime
count. Both nonzero-value exclusions remain visible for the offset locus. -/
theorem regular_fiber_tail (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (B Y : ℕ)
    (hY : 1<Y) (hx : normEliminant side κ t a d false≠0)
    (hz : normEliminant side κ t a d true≠0)
    (N M : ℝ) (hN : |(normEliminant side κ t a d false:ℝ)|≤N)
    (hM : |(normEliminant side κ t a d true:ℝ)|≤M) :
    (Nat.card (FiberBad side κ t a d B Y):ℝ)*Real.log (Y:ℝ)≤
      2*(Real.log N+Real.log M) := by
  have hc := finite_support_points side κ t a d B Y
    (support (normEliminant side κ t a d false) (normEliminant side κ t a d true) Y)
    (fun h p hp hYp _ _ ho => actual_affine_prime_cover side κ t a d Y hx hz h.1 p hp hYp ho)
  have hl := support_log_bound _ _ hx hz Y hY N M hN hM
  have hlog : 0≤Real.log (Y:ℝ) := (Real.log_pos (by exact_mod_cast hY)).le
  have hcR : (Nat.card (FiberBad side κ t a d B Y):ℝ)≤
      2*((support (normEliminant side κ t a d false) (normEliminant side κ t a d true) Y).card:ℝ) := by
    exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hcR hlog]

/-- The degenerate t=-2 second pair uses the UNPADDED positive linear/norm
eliminants. No zero-offset locus survives when both transverse entries are
nonzero; these entries are supplied by a successful second leading shear. -/
theorem exceptional_fiber_tail (κ t : ℤ) (ht2 : t+2=0) (a d : Vector ℤ)
    (hdx : d.1≠0) (hdz : d.2.1≠0) (B Y : ℕ) (hY : 2≤Y)
    (N M : ℝ)
    (hN : |(OriginalLinearNormEliminant318.eliminant t a.1 a.2.1 d.1 d.2.1:ℝ)|≤N)
    (hM : |(OriginalLinearNormEliminant318.eliminant t a.2.1 a.1 d.2.1 d.1:ℝ)|≤M) :
    (Nat.card (FiberBad true κ t a d B Y):ℝ)*Real.log (Y:ℝ)≤
      2*(Real.log N+Real.log M) := by
  let ex := OriginalLinearNormEliminant318.eliminant t a.1 a.2.1 d.1 d.2.1
  let ez := OriginalLinearNormEliminant318.eliminant t a.2.1 a.1 d.2.1 d.1
  have ht0 : t≠0 := by omega
  have hx : ex≠0 := (OriginalLinearNormEliminant318.positive t _ _ _ _ ht0 hdx).ne'
  have hz : ez≠0 := (OriginalLinearNormEliminant318.positive t _ _ _ _ ht0 hdz).ne'
  have hc := finite_support_points true κ t a d B Y (support ex ez Y) (by
    intro h p hp hYp hB hA ho
    letI : Fact p.Prime := ⟨hp⟩
    have htp : ¬(p:ℤ)∣t := by
      intro hdiv
      have ht : t = -2 := by omega
      have hpdiv : p∣2 := by
        have hh := Int.natAbs_dvd_natAbs.mpr hdiv
        simpa [ht] using hh
      have hp_le : p≤2 := Nat.le_of_dvd (by decide) hpdiv
      omega
    exact exceptional_affine_prime_cover κ t ht2 a d hdx hdz Y h.1 p htp hYp ho)
  have hl := support_log_bound ex ez hx hz Y (by omega) N M hN hM
  have hlog : 0≤Real.log (Y:ℝ) := (Real.log_pos (by exact_mod_cast (show 1<Y by omega))).le
  have hcR : (Nat.card (FiberBad true κ t a d B Y):ℝ)≤2*((support ex ez Y).card:ℝ) := by
    exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hcR hlog]

lemma exceptional_transverse (κ t : ℤ) (ht : t+2=0) (d : Vector ℤ) (p : ℕ)
    (ha : ¬(p:ℤ)∣fA true κ t d) : d.1≠0 ∧ d.2.1≠0 := by
  constructor
  · intro h
    apply ha
    simp [fA,ht,h]
  · intro h
    apply ha
    simp [fA,ht,h]

end OriginalAffinePointTail318
