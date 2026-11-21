module
public import ActualTZSharedFinePrimeMarker318
public section
noncomputable section
namespace ActualTZSharedFineHybridOffsetCap318
open scoped BigOperators
open ActualTZSharedFineHybridStencil318

/-- Actual common-x wrap cap with b active directions per
local test and a shared fine h. The number of local endpoint
pairs is t*b; the number of independent fine blocks is still t. -/
theorem off_bound (a t b s J M W Q n D C : ℕ) (hQ : Q*J≤n) (hC : W*M^2≤C*n)
    (A : Fin b→Fin s→ℤ) (hA : ∀ j k,|A j k|≤(W:ℤ)*(D:ℤ)) (w : Bits a t b)
    (z : Vals a t b s)
    (hG : ∀ i,|z (gpos i true)-z (gpos i false)|≤(J:ℤ))
    (hH : ∀ r k,|z (hpos r k)|≤(M:ℤ))
    (hL : ∀ r j,|z (lpos r j true)-z (lpos r j false)|≤2*(M:ℤ)) :
    |off Q A w z|≤((a+2*t*b*s*D*C:ℕ):ℤ)*(n:ℤ) := by
  unfold off
  refine (abs_add_le _ _).trans ?_
  have h1 : |∑ i : Fin a,if w (.inl i) then (Q:ℤ)*
        (z (gpos i true)-z (gpos i false)) else 0|≤(a:ℤ)*(n:ℤ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin a,(n:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · rw [abs_mul,abs_of_nonneg (by positivity : 0≤(Q:ℤ))]
          exact (mul_le_mul_of_nonneg_left (hG i) (by positivity)).trans (by exact_mod_cast hQ)
        · simp only [abs_zero,Nat.cast_nonneg]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have h2 (r : Fin t) (j : Fin b) :
      |∑ i : Fin s,A j i*z (hpos r i)|≤(s:ℤ)*(W:ℤ)*(D:ℤ)*(M:ℤ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin s,(W:ℤ)*(D:ℤ)*(M:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hA j i) (hH r i) (abs_nonneg _) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  have h3 : |∑ p : Fin t×Fin b,if w (.inr p) then
      (∑ k : Fin s,A p.2 k*z (hpos p.1 k))*(z (lpos p.1 p.2 true)-z (lpos p.1 p.2 false))
      else 0|≤(t:ℤ)*(b:ℤ)*(2*(s:ℤ)*(D:ℤ)*(C:ℤ)*(n:ℤ)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin t×Fin b,2*(s:ℤ)*(D:ℤ)*(C:ℤ)*(n:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · rw [abs_mul]
          have H := mul_le_mul (h2 i.1 i.2) (hL i.1 i.2) (abs_nonneg _) (by positivity)
          have hC' : (W:ℤ)*(M:ℤ)^2≤(C:ℤ)*(n:ℤ) := by exact_mod_cast hC
          refine H.trans ?_
          have H' := mul_le_mul_of_nonneg_left hC' (by positivity : 0≤2*(s:ℤ)*(D:ℤ))
          convert H' using 1 <;> ring
        · rw [abs_zero]; positivity
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_mul]
  refine (add_le_add h1 h3).trans_eq ?_
  push_cast
  ring

end ActualTZSharedFineHybridOffsetCap318
