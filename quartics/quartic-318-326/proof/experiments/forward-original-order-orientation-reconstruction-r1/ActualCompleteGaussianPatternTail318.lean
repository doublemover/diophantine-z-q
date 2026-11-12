module
public import ActualSamePositionWeightedTail318
public section
noncomputable section
namespace ActualCompleteGaussianPatternTail318
open scoped BigOperators
open ActualSamePositionDivisors318 ActualSamePositionWeightedTail318
open ActualGaussianPatternProjection318 ActualFiniteGaussianPositionTail318
set_option maxHeartbeats 17000000

@[expose] def SamePattern (B : ℕ) (ci : ℤ) (Y : ℕ) :=
  {z : ℤ×ℤ // ∃ v : Source B Y,
    v.1.2.2.1=z.2 ∧ v.1.1.1^2+v.1.2.1.1^2=z.1+ci*z.2^2}
@[expose] def sameChoice (B : ℕ) (ci : ℤ) (Y : ℕ) : SamePattern B ci Y → Source B Y :=
  fun z => z.2.choose
lemma same_w (B : ℕ) (ci : ℤ) (Y : ℕ) (z : SamePattern B ci Y) :
    (sameChoice B ci Y z).1.2.2.1=z.1.2 := z.2.choose_spec.1
lemma same_norm (B : ℕ) (ci : ℤ) (Y : ℕ) (z : SamePattern B ci Y) :
    (sameChoice B ci Y z).1.1.1^2+(sameChoice B ci Y z).1.2.1.1^2=z.1.1+ci*z.1.2^2 :=
  z.2.choose_spec.2
lemma sameChoice_injective (B : ℕ) (ci : ℤ) (Y : ℕ) : Function.Injective (sameChoice B ci Y) := by
  intro z z' he
  have hw : z.1.2=z'.1.2 := by
    have hh := congrArg (fun v : Source B Y => v.1.2.2.1) he
    simpa only [same_w] using hh
  have hn := same_norm B ci Y z
  have hn' := same_norm B ci Y z'
  rw [he,hw] at hn
  apply Subtype.ext
  exact Prod.ext (by linarith) hw
instance same_finite (B : ℕ) (ci : ℤ) (Y : ℕ) : Finite (SamePattern B ci Y) :=
  Finite.of_injective (sameChoice B ci Y) (sameChoice_injective B ci Y)

variable {J : Type*} [Fintype J] [DecidableEq J]
lemma same_weight_identity (B : ℕ) (ci : ℤ) (Y : ℕ) (c : J → ℤ) (z : SamePattern B ci Y) :
    tripleWeight (coefficients c ci) (sameChoice B ci Y z).1=patternWeight c z.1 := by
  apply Finset.prod_congr rfl
  intro j _
  have he : (sameChoice B ci Y z).1.1.1^2+(sameChoice B ci Y z).1.2.1.1^2+
      (coefficients c ci) j*(sameChoice B ci Y z).1.2.2.1^2=z.1.1+c j*z.1.2^2 := by
    rw [same_w,same_norm]
    dsimp [coefficients]
    ring
  rw [he]
@[expose] def sameMass (B : ℕ) (ci : ℤ) (Y : ℕ) (c : J → ℤ) : ℝ := by
  classical
  letI : Fintype (SamePattern B ci Y) := Fintype.ofFinite _
  exact ∑ z : SamePattern B ci Y,patternWeight c z.1
lemma actual_same_pattern_tail (B : ℕ) (hB : 1≤B) (ci : ℤ) (Y : ℕ)
    (hY : ActualGaussianGrowingCutoff318.cutoff 0 B≤Y) (c : J → ℤ) :
    sameMass B ci Y c≤sameConstant (coefficients c ci)*(B:ℝ)^(3-(1:ℝ)/200) := by
  classical
  letI : Fintype (SamePattern B ci Y) := Fintype.ofFinite _
  have hh := hasSum_le_inj (sameChoice B ci Y) (sameChoice_injective B ci Y)
    (fun v _ => tripleWeight_nonneg (coefficients c ci) v.1)
    (fun z => le_of_eq (same_weight_identity B ci Y c z).symm)
    (hasSum_fintype (fun z : SamePattern B ci Y => patternWeight c z.1))
    (hasSum_fintype (fun v : Source B Y => tripleWeight (coefficients c ci) v.1))
  exact hh.trans (actual_same_position_growing_tail B hB Y hY _)

/-- Single cutoff chosen from the fixed coefficient family and B BEFORE
any position, sign, generator or prime, covering both kinds of obstruction. -/
@[expose] def completeCutoff (c : J → ℤ) (B : ℕ) : ℕ :=
  max (commonCutoff c B) (ActualGaussianGrowingCutoff318.cutoff 0 B)
@[expose] def CompleteTarget (B Y : ℕ) (c : J → ℤ) :=
  PositionPattern B Y c ⊕ (Σ i : J,SamePattern B (c i) Y)
@[expose] def underlying (B Y : ℕ) (c : J → ℤ) : CompleteTarget B Y c → ℤ×ℤ :=
  Sum.elim Subtype.val (fun z => z.2.1)
/-- Original (u,w) admitting an actual large-common-prime obstruction,
either between distinct positions with arbitrary signs, or between the
two adjacent norms at the same position. Every generator choice is allowed. -/
@[expose] def CompletePattern (B Y : ℕ) (c : J → ℤ) :=
  {uw : ℤ×ℤ // ∃ z : CompleteTarget B Y c,underlying B Y c z=uw}
@[expose] def completeChoice (B Y : ℕ) (c : J → ℤ) :
    CompletePattern B Y c → CompleteTarget B Y c := fun z => z.2.choose
lemma complete_forget (B Y : ℕ) (c : J → ℤ) (z : CompletePattern B Y c) :
    underlying B Y c (completeChoice B Y c z)=z.1 := z.2.choose_spec
lemma complete_injective (B Y : ℕ) (c : J → ℤ) : Function.Injective (completeChoice B Y c) := by
  intro z z' he
  apply Subtype.ext
  have hh := congrArg (underlying B Y c) he
  simpa only [complete_forget] using hh
instance complete_finite (B Y : ℕ) (c : J → ℤ) : Finite (CompletePattern B Y c) :=
  Finite.of_injective (completeChoice B Y c) (complete_injective B Y c)
@[expose] def completeMass (B Y : ℕ) (c : J → ℤ) : ℝ := by
  classical
  letI : Fintype (CompletePattern B Y c) := Fintype.ofFinite _
  exact ∑ z : CompletePattern B Y c,patternWeight c z.1
@[expose] def completeConstant (c : J → ℤ) : ℝ :=
  positionConstant c+∑ i : J,sameConstant (coefficients c (c i))

/-- Complete ORIGINAL large-prime pattern upper bound. Both kinds of
source have been constructed and their original weights preserved. This
is not a medium-prime estimate and not a prime-producing lower bound. -/
theorem actual_complete_large_prime_pattern_tail (B : ℕ) (hB : 1≤B) (Y : ℕ)
    (c : J → ℤ) (hc : Function.Injective c) (hY : completeCutoff c B≤Y) :
    completeMass B Y c≤completeConstant c*(B:ℝ)^(3-(1:ℝ)/200) := by
  classical
  letI : Fintype (CompletePattern B Y c) := Fintype.ofFinite _
  letI : Fintype (PositionPattern B Y c) := Fintype.ofFinite _
  letI : ∀ i : J,Fintype (SamePattern B (c i) Y) := fun _ => Fintype.ofFinite _
  let wt : CompleteTarget B Y c → ℝ := fun z => patternWeight c (underlying B Y c z)
  have hh := hasSum_le_inj (completeChoice B Y c) (complete_injective B Y c)
    (fun z _ => patternWeight_nonneg c (underlying B Y c z))
    (fun z => le_of_eq (by dsimp [wt];rw [complete_forget]))
    (hasSum_fintype (fun z : CompletePattern B Y c => patternWeight c z.1)) (hasSum_fintype wt)
  have he : (∑ z : CompleteTarget B Y c,wt z)=positionMass B Y c+∑ i : J,sameMass B (c i) Y c := by
    simp only [CompleteTarget,Fintype.sum_sum_type,Fintype.sum_sigma,wt,underlying,
      Sum.elim_inl,Sum.elim_inr,positionMass,sameMass]
  rw [he] at hh
  have hdist := actual_all_distinct_positions_tail B hB Y c hc ((le_max_left _ _).trans hY)
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    actual_same_pattern_tail B hB (c i) Y ((le_max_right _ _).trans hY) c)
  rw [←Finset.sum_mul] at hs
  dsimp [completeConstant]
  nlinarith only [hh,hdist,hs]

/-- Literal same-position Gaussian data enter the final counted source. -/
theorem original_same_position_member (B Y : ℕ) (c : J → ℤ) (i : J)
    (u w a b : ℤ) (hn : a^2+b^2=u+c i*w^2)
    (ha : -(B:ℤ)≤a ∧ a≤B) (hb : -(B:ℤ)≤b ∧ b≤B) (hw : -(B:ℤ)≤w ∧ w≤B)
    (hbad : ∃ p : ℕ,p.Prime ∧ Y<p ∧ (p:ℤ)∣(a+1)^2+b^2 ∧ (p:ℤ)∣(a-1)^2+b^2) :
    ∃ z : CompletePattern B Y c,z.1=(u,w) := by
  let v : Source B Y := ⟨(⟨a,Finset.mem_Icc.mpr ha⟩,⟨b,Finset.mem_Icc.mpr hb⟩,
    ⟨w,Finset.mem_Icc.mpr hw⟩),hbad⟩
  let z : SamePattern B (c i) Y := ⟨(u,w),v,rfl,hn⟩
  exact ⟨⟨(u,w),Sum.inr ⟨i,z⟩,rfl⟩,rfl⟩

/-- The distinct-position original interface is retained in the COMPLETE
consumer, rather than stopping at an auxiliary source union. -/
theorem original_distinct_position_member (B Y : ℕ) (c : J → ℤ)
    (z : PositionPattern B Y c) :
    ∃ z' : CompletePattern B Y c,z'.1=z.1 :=
  ⟨⟨z.1,Sum.inl z,rfl⟩,rfl⟩

end ActualCompleteGaussianPatternTail318
