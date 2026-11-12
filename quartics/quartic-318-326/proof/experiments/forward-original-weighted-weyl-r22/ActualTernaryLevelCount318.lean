module
public import ActualDivisorSubpower318
public section
noncomputable section
namespace ActualTernaryLevelCount318
open scoped BigOperators
open IntegerResidueBoxCount318 TriangularLatticeBoxCount318 LiteralTernaryReduction318
open ActualIntegerFactorPairs318 ActualDivisorSubpower318 OriginalBadSliceLogWeight318
set_option maxHeartbeats 13000000

@[expose] def Level (B : ℕ) (κ v : ℤ) := {y : Box B // R κ (coordinates y)=v}
@[expose] def ZeroFibers (B : ℕ) (κ v : ℤ) :=
  {w : Interval B // κ*w.1^2-v=0}

/-- At most two actual integer w can make the xz right side zero.
No nonsquare assumption on kappa or v is needed. -/
lemma zero_fibers_count (B : ℕ) (κ v : ℤ) (hκ : κ≠0) :
    Nat.card (ZeroFibers B κ v)≤2 := by
  classical
  by_cases hn : Nonempty (ZeroFibers B κ v)
  · let a := Classical.choice hn
    have root (w : ZeroFibers B κ v) : w.1.1=a.1.1 ∨ w.1.1= -a.1.1 := by
      have hs : κ*w.1.1^2=κ*a.1.1^2 := by have hw := w.2;have ha := a.2;linarith
      have he := mul_left_cancel₀ hκ hs
      have hz : (w.1.1-a.1.1)*(w.1.1+a.1.1)=0 := by nlinarith only [he]
      rcases mul_eq_zero.mp hz with h|h
      · exact Or.inl (sub_eq_zero.mp h)
      · right;linarith
    let f : ZeroFibers B κ v → Bool := fun w => decide (w.1.1=a.1.1)
    have hf : Function.Injective f := by
      intro w z he
      apply Subtype.ext
      apply Subtype.ext
      by_cases hw : w.1.1=a.1.1
      · have hz : z.1.1=a.1.1 := by by_contra hh;simp [f,hw,hh] at he
        exact hw.trans hz.symm
      · have hz : z.1.1≠a.1.1 := by intro hh;simp [f,hw,hh] at he
        exact ((root w).resolve_left hw).trans ((root z).resolve_left hz).symm
    simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using Nat.card_le_card_of_injective f hf
  · letI : IsEmpty (ZeroFibers B κ v) := not_nonempty_iff.mp hn
    simp

/-- Exact fiber decomposition of the ORIGINAL ternary level, not a
replacement form with coefficient2 or a shifted source label. -/
@[expose] def levelEquiv (B : ℕ) (κ v : ℤ) :
    Level B κ v ≃ Σ w : Interval B, Pairs B (κ*w.1^2-v) where
  toFun y := ⟨y.1.2.2,⟨(y.1.1,y.1.2.1),by
    have h := y.2
    dsimp [R,coordinates] at h
    linarith⟩⟩
  invFun y := ⟨(y.2.1.1,y.2.1.2,y.1),by
    have h := y.2.2
    dsimp [R,coordinates]
    linarith⟩
  left_inv y := rfl
  right_inv y := rfl

@[expose] def levelHeight (B : ℕ) (κ v : ℤ) : ℝ :=
  |(κ:ℝ)|*(B:ℝ)^2+|(v:ℝ)|

lemma actual_fiber_height (B : ℕ) (κ v : ℤ) (w : Interval B) :
    |((κ*w.1^2-v:ℤ):ℝ)|≤levelHeight B κ v := by
  have hw := square_bound B w.1 (Finset.mem_Icc.mp w.2)
  have hwr : (w.1:ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast hw
  have hm := mul_le_mul_of_nonneg_left hwr (abs_nonneg (κ:ℝ))
  push_cast
  calc
    _ ≤ |(κ:ℝ)*(w.1:ℝ)^2|+|(v:ℝ)| := abs_sub _ _
    _ = |(κ:ℝ)|*(w.1:ℝ)^2+|(v:ℝ)| := by rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    _ ≤ levelHeight B κ v := by dsimp [levelHeight];linarith

/-- Constructed divisor-bound count on every original level R=v.
The zero right-hand-side fibers are counted separately and retained. -/
theorem actual_level_count (B : ℕ) (κ v : ℤ) (hκ : κ≠0) (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (Level B κ v):ℝ)≤
      (2*(B:ℝ)+1)*(2*divisorConstant δ*(levelHeight B κ v)^δ)+4*(2*(B:ℝ)+1) := by
  classical
  let n : Interval B → ℕ := fun w => Nat.card (Pairs B (κ*w.1^2-v))
  let bad : Interval B → Prop := fun w => κ*w.1^2-v=0
  let H := 2*divisorConstant δ*(levelHeight B κ v)^δ
  let K : ℝ := 2*(2*(B:ℝ)+1)
  have hH : 0≤H := by
    have hc := divisorConstant_pos δ hδ
    have hh : 0≤levelHeight B κ v := by dsimp [levelHeight];positivity
    dsimp [H]
    positivity
  have hgood (w : Interval B) (hw : ¬bad w) : (n w:ℝ)*1≤H := by
    have hn : κ*w.1^2-v≠0 := hw
    have hp : (n w:ℝ)≤2*((κ*w.1^2-v).natAbs.divisors.card:ℝ) := by
      exact_mod_cast actual_factor_count B (κ*w.1^2-v) hn
    have hd := actual_divisor_subpower δ hδ (κ*w.1^2-v).natAbs (Int.natAbs_ne_zero.mpr hn)
    have hnat : ((κ*w.1^2-v).natAbs:ℝ)=|((κ*w.1^2-v:ℤ):ℝ)| := by
      exact_mod_cast Int.natCast_natAbs (κ*w.1^2-v)
    have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(κ*w.1^2-v).natAbs)
      (by simpa only [hnat] using actual_fiber_height B κ v w) hδ.le
    have hm := mul_le_mul_of_nonneg_left hh (divisorConstant_pos δ hδ).le
    dsimp [H]
    nlinarith only [hp,hd,hm]
  have hbad (w : Interval B) (hw : bad w) : (n w:ℝ)*1≤K := by
    have hh := zero_factor_count B
    dsimp [n]
    rw [hw]
    dsimp [K]
    exact_mod_cast hh
  have hs := OriginalAffineRectangleTail318.sum_with_bad_fibers n bad 1 H K
    (by norm_num) hH (by dsimp [K];positivity) hgood hbad
  have hz : (Nat.card {w : Interval B // bad w}:ℝ)≤2 := by
    exact_mod_cast zero_fibers_count B κ v hκ
  have hzK := mul_le_mul_of_nonneg_right hz (by dsimp [K];positivity : 0≤K)
  have hc : (Nat.card (Level B κ v):ℝ)=∑ w : Interval B,(n w:ℝ) := by
    have hh := Nat.card_congr (levelEquiv B κ v)
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hh
    exact_mod_cast hh
  rw [←hc] at hs
  simp only [Interval,Fintype.card_coe,interval_card,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one,mul_one] at hs
  dsimp [H,K] at hs hzK
  nlinarith only [hs,hzK]

end ActualTernaryLevelCount318
