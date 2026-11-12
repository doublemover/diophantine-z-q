module
public import ActualCompleteGaussianPatternTail318
public import Mathlib.Algebra.BigOperators.Ring.Finset
public section
noncomputable section
namespace FiniteBernoulliEulerMoment318
open scoped BigOperators
set_option maxHeartbeats 15000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def factor (q : ℝ) (b : Bool) : ℝ := if b then q else 1-q
@[expose] def probability (q : ι → ℝ) (f : ι → Bool) : ℝ := ∏ i,factor (q i) (f i)
@[expose] def cost (l : ι → ℝ) (f : ι → Bool) : ℝ := ∑ i,if f i then l i else 0

lemma prod_one_site (i : ι) (u : ι → ℝ) : (∏ j,if j=i then u j else 1)=u i := by
  calc
    _ = (if i=i then u i else 1) := Finset.prod_eq_single i
      (fun j _ hji => if_neg hji) (fun hi => False.elim (hi (Finset.mem_univ i)))
    _ = _ := if_pos rfl

/-- Exact total mass on the ACTUAL finite Boolean choices, including the
empty prime index set. This is not an assumed independence model. -/
theorem probability_total (q : ι → ℝ) : (∑ f : ι → Bool,probability q f)=1 := by
  have hh := (Fintype.prod_sum (fun i (b : Bool) => factor (q i) b)).symm
  simpa [probability,factor,Fintype.sum_bool] using hh
lemma probability_nonneg (q : ι → ℝ) (hq : ∀ i,0≤q i ∧ q i≤1) (f : ι → Bool) :
    0≤probability q f := by
  apply Finset.prod_nonneg
  intro i _
  cases h : f i <;> simp only [factor,h,Bool.false_eq_true,if_false,if_true]
  · exact sub_nonneg.mpr (hq i).2
  · exact (hq i).1
lemma cost_nonneg (l : ι → ℝ) (hl : ∀ i,0≤l i) (f : ι → Bool) : 0≤cost l f := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hl i
  · exact le_rfl

/-- Each exact first moment is its original Bernoulli density times its
original log-prime cost, proved by finite product expansion. -/
lemma one_site_moment (q l : ι → ℝ) (i : ι) :
    (∑ f : ι → Bool,probability q f*(if f i then l i else 0))=q i*l i := by
  let marked := fun j (b : Bool) => factor (q j) b*(if j=i then (if b then l i else 0) else 1)
  have hpoint (f : ι → Bool) :
      (∏ j,marked j (f j))=probability q f*(if f i then l i else 0) := by
    dsimp [marked,probability]
    rw [Finset.prod_mul_distrib,prod_one_site]
  have hlocal (j : ι) : (∑ b : Bool,marked j b)=if j=i then q i*l i else 1 := by
    by_cases hji : j=i
    · subst j
      simp [marked,factor,Fintype.sum_bool]
    · simp [marked,hji,factor,Fintype.sum_bool]
  calc
    _ = ∑ f : ι → Bool,∏ j,marked j (f j) :=
      Finset.sum_congr rfl (fun f _ => (hpoint f).symm)
    _ = ∏ j,∑ b : Bool,marked j b := (Fintype.prod_sum marked).symm
    _ = ∏ j,if j=i then q i*l i else 1 := Finset.prod_congr rfl (fun j _ => hlocal j)
    _ = _ := prod_one_site i (fun _ => q i*l i)

theorem actual_first_moment (q l : ι → ℝ) :
    (∑ f : ι → Bool,probability q f*cost l f)=∑ i,q i*l i := by
  simp only [cost,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => one_site_moment q l i)

@[expose] def shortMass (q l : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ f : ι → Bool,if cost l f<L then probability q f else 0
@[expose] def longMass (q l : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ f : ι → Bool,if cost l f<L then 0 else probability q f
lemma mass_partition (q l : ι → ℝ) (L : ℝ) : shortMass q l L+longMass q l L=1 := by
  rw [shortMass,longMass,←Finset.sum_add_distrib]
  have he : (∑ f : ι → Bool,
      (if cost l f<L then probability q f else 0)+(if cost l f<L then 0 else probability q f))=
      ∑ f : ι → Bool,probability q f := by
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> simp
  rw [he,probability_total]

/-- Exact finite Markov truncation. Positivity and the actual first moment
are proved on the same finite choices; no analytic distribution law is
supplied. Strict cost<L is retained for the later strict divisor cutoff. -/
theorem actual_short_mass (q l : ι → ℝ) (hq : ∀ i,0≤q i ∧ q i≤1)
    (hl : ∀ i,0≤l i) (L : ℝ) (hL : 0<L) :
    1-(∑ i,q i*l i)/L≤shortMass q l L := by
  have hp (f : ι → Bool) : (if cost l f<L then 0 else probability q f)*L≤
      probability q f*cost l f := by
    by_cases hf : cost l f<L
    · simp only [hf,if_true,zero_mul]
      exact mul_nonneg (probability_nonneg q hq f) (cost_nonneg l hl f)
    · simp only [hf,if_false]
      exact mul_le_mul_of_nonneg_left (le_of_not_gt hf) (probability_nonneg q hq f)
  have hs := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => hp f)
  rw [←Finset.sum_mul,actual_first_moment] at hs
  change longMass q l L*L≤∑ i,q i*l i at hs
  have hd := (le_div_iff₀ hL).mpr hs
  have he := mass_partition q l L
  linarith

theorem actual_half_mass (q l : ι → ℝ) (hq : ∀ i,0≤q i ∧ q i≤1)
    (hl : ∀ i,0≤l i) (L : ℝ) (hL : 0<L)
    (hm : (∑ i,q i*l i)≤L/2) : 1/2≤shortMass q l L := by
  have hs := actual_short_mass q l hq hl L hL
  have hd : (∑ i,q i*l i)/L≤1/2 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  linarith

end FiniteBernoulliEulerMoment318
