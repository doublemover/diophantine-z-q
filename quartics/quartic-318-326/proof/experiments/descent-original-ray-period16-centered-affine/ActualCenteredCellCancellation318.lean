module
public import Mathlib
public section
noncomputable section
namespace ActualCenteredCellCancellation318

open scoped BigOperators

/-- T is the set of vertices carrying means, not the set carrying primes. -/
def hybrid {X V : Type*} [Fintype V] [DecidableEq V]
    (D : Finset X) (f : X → V → ℝ) (μ : V → ℝ) (T : Finset V) : ℝ :=
  (∑ x ∈ D, ∏ v ∈ Finset.univ \ T, f x v) * ∏ v ∈ T, μ v

/-- The same FT comparison main term is subtracted on every subset;
it cancels exactly, including the all-means (empty-prime) subset. -/
theorem centered_error {X V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Finset X) (f : X → V → ℝ) (μ : V → ℝ) (η : ℝ)
    (h : ∀ T ∈ (Finset.univ : Finset V).powerset,
      |hybrid D f μ T - (D.card:ℝ) * (∏ v : V, μ v)| ≤ η) :
    |∑ x ∈ D, ∏ v : V, (f x v - μ v)| ≤
      (2:ℝ)^(Fintype.card V) * η := by
  classical
  let P : Finset (Finset V) := (Finset.univ : Finset V).powerset
  let R : ℝ := (D.card:ℝ) * (∏ v : V, μ v)
  have hsplit : (∑ x ∈ D, ∏ v : V, (f x v - μ v)) =
      ∑ T ∈ P, (-1:ℝ)^T.card * hybrid D f μ T := by
    simp_rw [Finset.prod_sub]
    change (∑ x ∈ D, ∑ T ∈ P, (-1:ℝ)^T.card *
      (∏ v ∈ Finset.univ \ T, f x v) * (∏ v ∈ T, μ v)) = _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [hybrid, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.sum_mul,mul_assoc]
  have hcancel : (∑ T ∈ P, (-1:ℝ)^T.card * R) = 0 := by
    have hsign : (∑ T ∈ P, (-1:ℝ)^T.card)=0 := by
      have he := Finset.prod_sub (fun _ : V => (1:ℝ)) (fun _ : V => 1) Finset.univ
      have hz : (∏ v : V, ((1:ℝ)-1))=0 := by
        obtain ⟨v⟩ := ‹Nonempty V›
        exact Finset.prod_eq_zero (Finset.mem_univ v) (sub_self 1)
      rw [hz] at he
      simpa only [P,Finset.prod_const_one,mul_one] using he.symm
    rw [← Finset.sum_mul,hsign,zero_mul]
  have hid : (∑ T ∈ P, (-1:ℝ)^T.card * hybrid D f μ T) =
      ∑ T ∈ P, (-1:ℝ)^T.card * (hybrid D f μ T - R) := by
    simp only [mul_sub,Finset.sum_sub_distrib,hcancel,sub_zero]
  rw [hsplit,hid]
  calc
    _ ≤ ∑ T ∈ P, |(-1:ℝ)^T.card * (hybrid D f μ T - R)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ P, η := by
      apply Finset.sum_le_sum
      intro T hT
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using h T hT
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,P,Finset.card_powerset,
      Finset.card_univ,Nat.cast_pow,Nat.cast_ofNat]

end ActualCenteredCellCancellation318
