module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public section
noncomputable section
namespace ActualRayPeriodicRectangle318

open scoped BigOperators

@[expose] def line (f : ℕ → ℝ) (a n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f (a+i)

@[expose] def rectangle (f : ℕ → ℕ → ℝ) (a b n m : ℕ) : ℝ :=
  line (fun i => line (f i) b m) a n

@[expose] def Periods (E : ℕ) (f : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, f (i+E) j=f i j) ∧ ∀ i j, f i (j+E)=f i j

theorem line_add (f : ℕ → ℝ) (a n m : ℕ) :
    line f a (n+m)=line f a n + line f (a+n) m := by
  unfold line
  rw [Finset.sum_range_add] <;> simp only [Nat.add_assoc]

theorem line_add_fn (f g : ℕ → ℝ) (a n : ℕ) :
    line (fun i => f i+g i) a n=line f a n+line g a n := by
  simp only [line,Finset.sum_add_distrib]

theorem line_scale (f : ℕ → ℝ) (q : ℝ) (a n : ℕ) :
    line (fun i => q*f i) a n=q*line f a n := by
  simp only [line,Finset.mul_sum]

theorem line_one (f : ℕ → ℝ) (a : ℕ) : line f a 1=f a := by
  simp only [line,Finset.sum_range_one,Nat.add_zero]

theorem line_period_shift (f : ℕ → ℝ) (E : ℕ) (hf : ∀ a, f (a+E)=f a) (a : ℕ) :
    line f (a+1) E=line f a E := by
  have h1 := line_add f a 1 E
  have h2 := line_add f a E 1
  rw [Nat.add_comm 1 E] at h1
  rw [h1] at h2
  simp only [line_one,hf a] at h2
  linarith only [h2]

theorem line_period_block (f : ℕ → ℝ) (E : ℕ) (hf : ∀ a, f (a+E)=f a) (a : ℕ) :
    line f a E=line f 0 E := by
  induction a with
  | zero => rfl
  | succ a h => exact (line_period_shift f E hf a).trans h

theorem line_full (f : ℕ → ℝ) (E : ℕ) (hf : ∀ a, f (a+E)=f a) (a k : ℕ) :
    line f a (k*E)=(k:ℝ)*line f 0 E := by
  induction k with
  | zero => simp [line]
  | succ k ih =>
      rw [Nat.succ_mul,line_add,ih,line_period_block f E hf,
        Nat.cast_succ,add_mul,one_mul]

theorem rectangle_split_x (f : ℕ → ℕ → ℝ) (a b n₀ n₁ m : ℕ) :
    rectangle f a b (n₀+n₁) m=rectangle f a b n₀ m+rectangle f (a+n₀) b n₁ m :=
  line_add _ _ _ _

theorem rectangle_split_y (f : ℕ → ℕ → ℝ) (a b n m₀ m₁ : ℕ) :
    rectangle f a b n (m₀+m₁)=rectangle f a b n m₀+rectangle f a (b+m₀) n m₁ := by
  unfold rectangle
  rw [←line_add_fn]
  exact congrArg (fun g => line g a n) (funext fun i => line_add (f i) b m₀ m₁)

theorem rectangle_full (f : ℕ → ℕ → ℝ) (E : ℕ) (hf : Periods E f)
    (a b k l : ℕ) :
    rectangle f a b (k*E) (l*E)=(k:ℝ)*(l:ℝ)*rectangle f 0 0 E E := by
  let g (i : ℕ) := line (f i) b (l*E)
  have hg (i : ℕ) : g (i+E)=g i :=
    congrArg (fun u => line u b (l*E)) (funext (hf.1 i))
  have hInner : g=(fun i => (l:ℝ)*line (f i) 0 E) := by
    funext i
    exact line_full (f i) E (hf.2 i) b l
  calc
    rectangle f a b (k*E) (l*E)=(k:ℝ)*line g 0 E := line_full g E hg a k
    _=(k:ℝ)*((l:ℝ)*rectangle f 0 0 E E) := by
      rw [hInner,line_scale] <;> rfl
    _=_ := (mul_assoc _ _ _).symm

theorem line_bound (f : ℕ → ℝ) (a n : ℕ) (A : ℝ) (hf : ∀ i, 0≤f i ∧ f i≤A) :
    0≤line f a n ∧ line f a n≤(n:ℝ)*A := by
  unfold line
  constructor
  · exact Finset.sum_nonneg fun i _ => (hf (a+i)).1
  · calc
      (∑ i ∈ Finset.range n, f (a+i)) ≤ ∑ _i ∈ Finset.range n, A :=
        Finset.sum_le_sum fun i _ => (hf (a+i)).2
      _ = (n:ℝ)*A := by simp [nsmul_eq_mul]

theorem rectangle_bound (f : ℕ → ℕ → ℝ) (a b n m : ℕ) (A : ℝ)
    (hf : ∀ i j, 0≤f i j ∧ f i j≤A) :
    0≤rectangle f a b n m ∧ rectangle f a b n m≤(n:ℝ)*(m:ℝ)*A := by
  have h := line_bound (fun i => line (f i) b m) a n ((m:ℝ)*A)
    (fun i => line_bound (f i) b m A (hf i))
  simpa only [rectangle,mul_assoc] using h

@[expose] def mean (f : ℕ → ℕ → ℝ) (E : ℕ) : ℝ :=
  rectangle f 0 0 E E / (E:ℝ)^2

/-- Exact disjoint decomposition: horizontal strip includes its full
height; the remaining vertical strip uses only the full block width.
No omitted corner is double counted. -/
theorem rectangle_quotient_decomposition (f : ℕ → ℕ → ℝ) (E : ℕ)
    (hf : Periods E f) (a b n m : ℕ) :
    rectangle f a b n m =
      ((n/E:ℕ):ℝ)*((m/E:ℕ):ℝ)*rectangle f 0 0 E E +
      rectangle f a (b+(m/E)*E) ((n/E)*E) (m%E) +
      rectangle f (a+(n/E)*E) b (n%E) m := by
  have hn := Nat.div_add_mod' n E
  have hm := Nat.div_add_mod' m E
  calc
    rectangle f a b n m =
        rectangle f a b ((n/E)*E) m + rectangle f (a+(n/E)*E) b (n%E) m := by
      simpa only [hn] using rectangle_split_x f a b ((n/E)*E) (n%E) m
    _=_ := by
      have hY := rectangle_split_y f a b ((n/E)*E) ((m/E)*E) (m%E)
      rw [hm] at hY
      rw [hY,rectangle_full f E hf]

/-- Fixed error constant for arbitrary starts and both lengths. The
two missing strip contributions and their proportional means are
independently in the same interval, so no factor of two is necessary. -/
theorem rectangle_mean_error_exact (f : ℕ → ℕ → ℝ) (E : ℕ) (hE : 0<E)
    (hf : Periods E f) (a b n m : ℕ) (A : ℝ)
    (hval : ∀ i j, 0≤f i j ∧ f i j≤A) :
    |rectangle f a b n m-(n:ℝ)*(m:ℝ)*mean f E| ≤
      ((((n/E)*E:ℕ):ℝ)*((m%E:ℕ):ℝ)+((n%E:ℕ):ℝ)*(m:ℝ))*A := by
  let n₀ := (n/E)*E
  let m₀ := (m/E)*E
  let n₁ := n%E
  let m₁ := m%E
  let μ := mean f E
  let T : ℝ := (n₀:ℝ)*(m₁:ℝ)+(n₁:ℝ)*(m:ℝ)
  let core : ℝ := (n₀:ℝ)*(m₀:ℝ)*μ
  let U := rectangle f a (b+m₀) n₀ m₁
  let V := rectangle f (a+n₀) b n₁ m
  have hE' : 0<(E:ℝ) := by exact_mod_cast hE
  have hden : 0<(E:ℝ)^2 := pow_pos hE' _
  have hBlock := rectangle_bound f 0 0 E E A hval
  have hμ0 : 0≤μ := div_nonneg hBlock.1 hden.le
  have hμA : μ≤A := by
    change mean f E ≤ A
    unfold mean
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (E:ℝ)*(E:ℝ)*A := hBlock.2
      _ = A*(E:ℝ)^2 := by ring
  have hCore : ((n/E:ℕ):ℝ)*((m/E:ℕ):ℝ)*rectangle f 0 0 E E=core := by
    unfold core n₀ m₀ μ mean
    simp only [Nat.cast_mul]
    field_simp [hE'.ne'] <;> ring
  have hRect : rectangle f a b n m=core+U+V := by
    rw [rectangle_quotient_decomposition f E hf a b n m,hCore] <;> rfl
  have hU := rectangle_bound f a (b+m₀) n₀ m₁ A hval
  have hV := rectangle_bound f (a+n₀) b n₁ m A hval
  have hUV0 : 0≤U+V := add_nonneg hU.1 hV.1
  have hUV1 : U+V≤T*A := by
    change U+V≤((n₀:ℝ)*(m₁:ℝ)+(n₁:ℝ)*(m:ℝ))*A
    rw [add_mul]
    exact add_le_add hU.2 hV.2
  have hn : (n₀:ℝ)+(n₁:ℝ)=(n:ℝ) := by
    exact_mod_cast Nat.div_add_mod' n E
  have hm : (m₀:ℝ)+(m₁:ℝ)=(m:ℝ) := by
    exact_mod_cast Nat.div_add_mod' m E
  have hT : (n:ℝ)*(m:ℝ)=(n₀:ℝ)*(m₀:ℝ)+T := by
    unfold T
    linear_combination -(m:ℝ)*hn-(n₀:ℝ)*hm
  have hMean : (n:ℝ)*(m:ℝ)*mean f E=core+T*μ := by
    change (n:ℝ)*(m:ℝ)*μ= _
    rw [hT,add_mul] <;> rfl
  have hT0 : 0≤T := by unfold T; positivity
  have hTμ0 : 0≤T*μ := mul_nonneg hT0 hμ0
  have hTμA : T*μ≤T*A := mul_le_mul_of_nonneg_left hμA hT0
  change |_ - _|≤T*A
  rw [hRect,hMean,abs_le]
  constructor <;> linarith only [hUV0,hUV1,hTμ0,hTμA]

theorem rectangle_mean_error (f : ℕ → ℕ → ℝ) (E : ℕ) (hE : 0<E)
    (hf : Periods E f) (a b n m : ℕ) (A : ℝ)
    (hval : ∀ i j, 0≤f i j ∧ f i j≤A) :
    |rectangle f a b n m-(n:ℝ)*(m:ℝ)*mean f E|≤
      (E:ℝ)*((n:ℝ)+(m:ℝ))*A := by
  have hA : 0≤A := (hval 0 0).1.trans (hval 0 0).2
  have hn₀ : (n/E)*E≤n := by
    have h := Nat.div_add_mod' n E
    omega
  have hWidth : (((n/E)*E:ℕ):ℝ)*((m%E:ℕ):ℝ)+((n%E:ℕ):ℝ)*(m:ℝ) ≤
      (E:ℝ)*((n:ℝ)+(m:ℝ)) := by
    have h1 : (((n/E)*E:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hn₀
    have h2 : ((m%E:ℕ):ℝ) ≤ (E:ℝ) := by exact_mod_cast (Nat.mod_lt m hE).le
    have h3 : ((n%E:ℕ):ℝ) ≤ (E:ℝ) := by exact_mod_cast (Nat.mod_lt n hE).le
    calc
      _≤ (n:ℝ)*(E:ℝ)+(E:ℝ)*(m:ℝ) :=
        add_le_add (mul_le_mul h1 h2 (by positivity) (by positivity))
          (mul_le_mul_of_nonneg_right h3 (by positivity))
      _=_ := by ring
  exact (rectangle_mean_error_exact f E hE hf a b n m A hval).trans
    (mul_le_mul_of_nonneg_right hWidth hA)

end ActualRayPeriodicRectangle318
