module
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Field
public section
noncomputable section
namespace ActualLinearQFiniteRayMean318
open scoped BigOperators
open Classical

/-- The q form removes y=0. At fixed remaining y, each merged contact
slope removes one distinct x. -/
@[expose] def GoodRow {F : Type*} [Field F] [Fintype F] (S : Finset F) (y : F) : Finset F :=
  Finset.univ.filter (fun x => ∀ k ∈ S, x+k*y ≠ 0)

theorem goodRow_card {F : Type*} [Field F] [Fintype F] (S : Finset F)
    {y : F} (hy : y ≠ 0) : (GoodRow S y).card = Fintype.card F-S.card := by
  classical
  have hinj : Function.Injective (fun k : F => -(k*y)) := by
    intro a b h
    have hm : a*y = b*y := neg_injective h
    exact mul_right_cancel₀ hy hm
  have hS : GoodRow S y = Finset.univ \ S.image (fun k => -(k*y)) := by
    ext x
    simp only [GoodRow,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,Finset.mem_image]
    constructor
    · intro hn he
      obtain ⟨k,hk,rfl⟩ := he
      exact hn k hk (neg_add_cancel _)
    · intro hn k hk hx
      apply hn
      exact ⟨k,hk,by
        have e : x = -(k*y) := by linear_combination hx
        exact e.symm⟩
  rw [hS,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    Finset.card_image_of_injective S hinj]

/-- Complete two-dimensional ordinary wheel count. For the actual
coefficient image, its size is unchanged at primes off the fixed minors. -/
theorem goodPair_card {F : Type*} [Field F] [Fintype F] (S : Finset F) :
    ((Finset.univ.erase (0:F)).sigma (fun y => GoodRow S y)).card =
      (Fintype.card F-1)*(Fintype.card F-S.card) := by
  rw [Finset.card_sigma]
  calc
    _ = ∑ y ∈ (Finset.univ : Finset F).erase 0, (Fintype.card F-S.card) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact goodRow_card S ((Finset.mem_erase.mp hy).1)
    _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_univ (0:F))]

/-- Exact normalized ordinary factor at a new odd prime. -/
theorem goodPair_weight {F : Type*} [Field F] [Fintype F] (S : Finset F) :
    (∑ _ ∈ (Finset.univ.erase (0:F)).sigma (fun y => GoodRow S y),
       ((Fintype.card F:ℝ)/((Fintype.card F:ℝ)-1))^(1+S.card)) /
      (Fintype.card F:ℝ)^2 =
    ((((Fintype.card F-1)*(Fintype.card F-S.card):ℕ):ℝ) /
      (Fintype.card F:ℝ)^2) *
      ((Fintype.card F:ℝ)/((Fintype.card F:ℝ)-1))^(1+S.card) := by
  rw [Finset.sum_const,nsmul_eq_mul,goodPair_card]
  ring

/-- Split Gaussian norm fibre xy=n, parameterized by nonzero x. The
translated-zero tests are EXACTLY the four possible x roots ±1, ±n,
allowing collisions when n=±1. -/
theorem split_bad_iff {F : Type*} [Field F] (x n : F) (hx : x ≠ 0) :
    (x-1)*(n/x-1)=0 ∨ (x+1)*(n/x+1)=0 ↔
      x=1 ∨ x= -1 ∨ x=n ∨ x= -n := by
  constructor
  · intro h
    rcases h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · have hn := (div_eq_iff hx).mp (sub_eq_zero.mp h)
        exact Or.inr (Or.inr (Or.inl (by simpa only [one_mul] using hn.symm)))
    · rcases mul_eq_zero.mp h with h | h
      · right; left; linear_combination h
      · have hd : n/x = -1 := by linear_combination h
        have hn := (div_eq_iff hx).mp hd
        right; right; right
        simp only [neg_one_mul] at hn
        simpa only [neg_neg] using (congrArg (fun z : F => -z) hn).symm
  · rintro (rfl | rfl | rfl | rfl)
    · left; simp
    · right; simp
    · left; simp [hx]
    · right
      have hd : n/(-n) = -1 := by apply (div_eq_iff hx).2; ring
      rw [hd]
      ring

/-- Conditional local ray refinement: H is the common norm-fibre size
(p ± 1); take bad=4 in the split case and bad=2 in the inert case. -/
theorem fibre_product_lower {V : Type*} [Fintype V]
    (safe : V → ℕ) (H bad : ℕ) (hH : 0 < H) (hbad : bad ≤ H)
    (hSafe : ∀ v, H-bad ≤ safe v) :
    (1-(bad:ℝ)/(H:ℝ))^Fintype.card V ≤ ∏ v, ((safe v:ℝ)/(H:ℝ)) := by
  have hh : 0 < (H:ℝ) := by exact_mod_cast hH
  have hb : (bad:ℝ) ≤ (H:ℝ) := by exact_mod_cast hbad
  calc
    _ = ∏ _ : V, (1-(bad:ℝ)/(H:ℝ)) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro v hv
        have hdiv := (div_le_iff₀ hh).2 (show (bad:ℝ) ≤ 1*(H:ℝ) by simpa using hb)
        linarith only [hdiv]
      · intro v hv
        have hh' : ((H-bad:ℕ):ℝ) ≤ (safe v:ℝ) := by exact_mod_cast hSafe v
        rw [Nat.cast_sub hbad] at hh'
        apply (le_div_iff₀ hh).2
        rw [sub_mul,one_mul,div_mul_cancel₀ _ hh.ne']
        exact hh'

/-- Inert place: a translated norm is zero only at the appropriate
unit itself. Within a norm fibre this removes at most two actual elements. -/
theorem inert_zero {F : Type*} [Field F] (hI : ∀ z : F, z^2 ≠ -1) (a b : F) :
    a^2+b^2=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    have hb : b=0 := by
      by_contra hb
      apply hI (a/b)
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      linear_combination h
    refine ⟨?_,hb⟩
    subst b
    have ha : a^2=0 := by simpa using h
    by_contra ha0
    exact (pow_ne_zero 2 ha0) ha
  · rintro ⟨rfl,rfl⟩
    norm_num

theorem inert_bad_iff {F : Type*} [Field F] (hI : ∀ z : F, z^2 ≠ -1) (a b : F) :
    (a-1)^2+b^2=0 ∨ (a+1)^2+b^2=0 ↔ (a=1 ∨ a= -1) ∧ b=0 := by
  rw [inert_zero hI,inert_zero hI]
  constructor
  · rintro (⟨h,hb⟩ | ⟨h,hb⟩)
    · exact ⟨Or.inl (sub_eq_zero.mp h),hb⟩
    · exact ⟨Or.inr (by linear_combination h),hb⟩
  · rintro ⟨(rfl | rfl),rfl⟩ <;> simp

/-- Refinement of a literal finite complete-residue average by the
conditional fibre counts, one per merged genuine form. No prime
asymptotic, unregulated limit, or growing-field estimate is used here. -/
theorem conditional_ordinary_mean_lower {I V : Type*} [Fintype V]
    (S : Finset I) (safe : I → V → ℕ) (H bad : ℕ) (w den : ℝ)
    (hH : 0 < H) (hbad : bad ≤ H) (hw : 0 ≤ w) (hd : 0 < den)
    (hSafe : ∀ x ∈ S, ∀ v, H-bad ≤ safe x v) :
    (((S.card:ℝ)*w)/den)*(1-(bad:ℝ)/(H:ℝ))^Fintype.card V ≤
      (∑ x ∈ S, w*(∏ v, ((safe x v:ℝ)/(H:ℝ))))/den := by
  let l := (1-(bad:ℝ)/(H:ℝ))^Fintype.card V
  have hsum : (∑ _ ∈ S, w*l) ≤ ∑ x ∈ S, w*(∏ v, ((safe x v:ℝ)/(H:ℝ))) := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (fibre_product_lower _ H bad hH hbad (hSafe x hx)) hw
  have hdiv := div_le_div_of_nonneg_right hsum hd.le
  rw [Finset.sum_const,nsmul_eq_mul] at hdiv
  change (S.card:ℝ)*w/den*l ≤ _
  convert hdiv using 1 <;> ring

/-- Exact rank-four norm-pair mass on an off-minors sieve prime.
This is the local count BEFORE intersections between distinct forms;
their nonparallelity forces both displayed norm values to be zero. -/
theorem rankFour_mass (p χ : ℤ) (hχ : χ^2 = 1) :
    (p+(p-1)*χ)^2+(p-1)*(p-χ)^2 = p^3+p^2-p := by
  linear_combination p*(p-1)*hχ

/-- The diagonal opposite-neighbor slice is not two independent norm
equations. At every odd prime it forces a=0 and b²=-1. -/
theorem diagonal_opposite {F : Type*} [Field F] (h2 : (2:F) ≠ 0) (a b : F) :
    ((a-1)^2+b^2=0 ∧ (a+1)^2+b^2=0) ↔ a=0 ∧ b^2= -1 := by
  constructor
  · rintro ⟨hm,hp⟩
    have h4a : (2:F)*2*a = 0 := by linear_combination hp - hm
    have ha : a=0 := (mul_eq_zero.mp h4a).resolve_left (mul_ne_zero h2 h2)
    subst a
    exact ⟨rfl,by linear_combination hp⟩
  · rintro ⟨rfl,hb⟩
    constructor <;> linear_combination hb

end ActualLinearQFiniteRayMean318
