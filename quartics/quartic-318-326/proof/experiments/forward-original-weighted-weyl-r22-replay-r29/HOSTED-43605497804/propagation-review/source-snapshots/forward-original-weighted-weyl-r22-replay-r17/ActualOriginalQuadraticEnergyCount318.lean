module
public import ActualOriginalSquareDifferenceFibers318
public import ActualTernaryLevelCount318
public section
noncomputable section
namespace ActualOriginalQuadraticEnergyCount318
open IntegerResidueBoxCount318 ActualOriginalSquareDifferenceFibers318
open ActualDivisorSubpower318 OriginalBadSliceLogWeight318
open scoped BigOperators

@[expose] def difference (H : ℕ) (p : Interval H×Interval H) : ℤ := p.1.1^2-p.2.1^2
@[expose] def Energy (H : ℕ) :=
  {p : (Interval H×Interval H)×(Interval H×Interval H) // difference H p.1=difference H p.2}
@[expose] def energyEquiv (H : ℕ) : Energy H ≃ Σ p : Interval H×Interval H, SquarePairs H (difference H p) where
  toFun p := ⟨p.1.1,⟨p.1.2,p.2.symm⟩⟩
  invFun p := ⟨(p.1,p.2.1),p.2.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma actual_difference_height (H : ℕ) (p : Interval H×Interval H) :
    |difference H p|≤(H : ℤ)^2 := by
  have hx := square_bound H p.1.1 (Finset.mem_Icc.mp p.1.2)
  have hy := square_bound H p.2.1 (Finset.mem_Icc.mp p.2.2)
  apply abs_le.mpr
  dsimp [difference]
  constructor <;> nlinarith [sq_nonneg p.1.1,sq_nonneg p.2.1]

@[expose] def momentBudget (H : ℕ) (δ : ℝ) : ℝ :=
  (2*(H : ℝ)+1)^2*(2*divisorConstant δ*((H : ℝ)^2)^δ+4)

lemma actual_moment_budget_nonneg (H : ℕ) (δ : ℝ) (hδ : 0<δ) : 0≤momentBudget H δ := by
  have hc := divisorConstant_pos δ hδ
  unfold momentBudget
  positivity

/-- A produced O(H^(2+2delta)) quadratic fourth-moment counting budget.
All signs and the zero-difference stratum are retained. -/
theorem actual_quadratic_energy_count (H : ℕ) (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (Energy H) : ℝ)≤momentBudget H δ := by
  classical
  let n : Interval H×Interval H → ℕ := fun p => Nat.card (SquarePairs H (difference H p))
  let bad : Interval H×Interval H → Prop := fun p => difference H p=0
  let A := 2*divisorConstant δ*((H : ℝ)^2)^δ
  let K : ℝ := 2*(2*(H : ℝ)+1)
  have hA : 0≤A := by have hc := divisorConstant_pos δ hδ; dsimp [A];positivity
  have hK : 0≤K := by dsimp [K];positivity
  have hg (p : Interval H×Interval H) (hp : ¬bad p) : (n p : ℝ)*1≤A := by
    have hn : difference H p≠0 := hp
    have hc : (n p : ℝ)≤2*((difference H p).natAbs.divisors.card : ℝ) := by
      exact_mod_cast actual_nonzero_square_pair_count H (difference H p) hn
    have hd := actual_divisor_subpower δ hδ (difference H p).natAbs (Int.natAbs_ne_zero.mpr hn)
    have hcast : ((difference H p).natAbs : ℝ)=|(difference H p : ℝ)| := by
      exact_mod_cast Int.natCast_natAbs (difference H p)
    have hheight : |(difference H p : ℝ)|≤(H : ℝ)^2 := by exact_mod_cast actual_difference_height H p
    have hm := Real.rpow_le_rpow (abs_nonneg (difference H p : ℝ)) hheight hδ.le
    rw [hcast] at hd
    have hh := mul_le_mul_of_nonneg_left hm (divisorConstant_pos δ hδ).le
    dsimp [A]
    nlinarith only [hc,hd,hh]
  have hb (p : Interval H×Interval H) (hp : bad p) : (n p : ℝ)*1≤K := by
    dsimp [n]
    rw [hp]
    dsimp [K]
    exact_mod_cast actual_zero_square_pair_count H
  have hs := OriginalAffineRectangleTail318.sum_with_bad_fibers n bad 1 A K
    (by norm_num) hA hK hg hb
  have hz : (Nat.card {p : Interval H×Interval H // bad p} : ℝ)≤K := by
    exact_mod_cast actual_zero_square_pair_count H
  have hzK := mul_le_mul_of_nonneg_right hz hK
  have he : (Nat.card (Energy H) : ℝ)=∑ p : Interval H×Interval H, (n p : ℝ) := by
    have hh := Nat.card_congr (energyEquiv H)
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hh
    exact_mod_cast hh
  rw [←he] at hs
  simp only [Fintype.card_prod,Interval,Fintype.card_coe,OriginalOffsetZeroLocus318.interval_card,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one] at hs
  dsimp [momentBudget,A,K] at hs hzK ⊢
  nlinarith only [hs,hzK]

end ActualOriginalQuadraticEnergyCount318
