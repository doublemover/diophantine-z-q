module
public import MvPolynomialEvaluationGrowth318
public section
noncomputable section
namespace PolynomialWeightBounds318
variable {X : Type*} (W : X → ℝ)

/-- A uniform polynomial bound in one fixed positive weight. -/
def Bounded (f : X → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x, f x ≤ C * W x ^ N

variable {W}
theorem mono {f g : X → ℝ} (hg : Bounded W g) (hfg : ∀ x, f x ≤ g x) :
    Bounded W f := by
  obtain ⟨C,hC,N,hg⟩ := hg
  exact ⟨C,hC,N,fun x => (hfg x).trans (hg x)⟩

theorem const (c : ℝ) : Bounded W (fun _ => c) := by
  exact ⟨max c 0,le_max_right _ _,0,by intro x; simpa using le_max_left c 0⟩

theorem weight : Bounded W W := ⟨1,zero_le_one,1,by intro x; simp⟩

theorem add (hW : ∀ x, 1 ≤ W x) {f g : X → ℝ}
    (hf : Bounded W f) (hg : Bounded W g) : Bounded W (fun x => f x+g x) := by
  obtain ⟨C,hC,N,hf⟩ := hf
  obtain ⟨D,hD,M,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,N+M,?_⟩
  intro x
  calc
    f x+g x ≤ C*W x^N+D*W x^M := add_le_add (hf x) (hg x)
    _ ≤ C*W x^(N+M)+D*W x^(N+M) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hW x) (Nat.le_add_right _ _)) hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hW x) (Nat.le_add_left _ _)) hD)
    _ = (C+D)*W x^(N+M) := by ring

theorem mul (hW : ∀ x, 0 ≤ W x) {f g : X → ℝ}
    (hf : Bounded W f) (hg : Bounded W g) (hg0 : ∀ x, 0 ≤ g x) :
    Bounded W (fun x => f x*g x) := by
  obtain ⟨C,hC,N,hf⟩ := hf
  obtain ⟨D,hD,M,hg⟩ := hg
  refine ⟨C*D,mul_nonneg hC hD,N+M,?_⟩
  intro x
  calc
    f x*g x ≤ (C*W x^N)*(D*W x^M) :=
      mul_le_mul (hf x) (hg x) (hg0 x) (mul_nonneg hC (pow_nonneg (hW x) _))
    _ = (C*D)*W x^(N+M) := by rw [pow_add]; ring

theorem pow (hW : ∀ x, 0 ≤ W x) {f : X → ℝ}
    (hf : Bounded W f) (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) :
    Bounded W (fun x => f x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using (const (W := W) 1)
  | succ n ih =>
      simpa only [pow_succ] using mul hW ih hf hf0

theorem sum (hW : ∀ x, 1 ≤ W x) {I : Type*} (s : Finset I) (f : I → X → ℝ)
    (hf : ∀ i ∈ s, Bounded W (f i)) : Bounded W (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (W := W) 0)
  | @insert i s hi ih =>
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        add hW (hf i (Finset.mem_insert_self i s)) hs

/-- One bound for a finite collection, retaining the same weight. -/
theorem uniform (hW : ∀ x, 1 ≤ W x) {I : Type*} (s : Finset I) (f : I → X → ℝ)
    (hf : ∀ i, Bounded W (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i ∈ s, ∀ x, f i x ≤ C*W x^N := by
  classical
  choose C hC N h using hf
  refine ⟨∑ i ∈ s, C i,Finset.sum_nonneg (fun i _ => hC i),s.sup N,?_⟩
  intro i hi x
  exact (h i x).trans (mul_le_mul
    (Finset.single_le_sum (fun j _ => hC j) hi)
    (pow_le_pow_right₀ (hW x) (Finset.le_sup (f := N) hi))
    (pow_nonneg (le_trans zero_le_one (hW x)) _)
    (Finset.sum_nonneg (fun j _ => hC j)))
end PolynomialWeightBounds318
