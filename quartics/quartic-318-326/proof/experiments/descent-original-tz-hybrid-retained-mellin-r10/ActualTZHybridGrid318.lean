module
public import ActualTZHybridGlobalLocalStencil318
public import ActualTZExactZeroIntegerGrid318
public import ActualTZOneAxisLocalDual318
public import ActualTZGlobalCubeAnchor318
import all ActualTZExactZeroIntegerGrid318
public section
noncomputable section
namespace ActualTZHybridGrid318
open scoped BigOperators
open ActualTZHybridGlobalLocalStencil318 ActualTZExactZeroIntegerGrid318
open ActualTZGlobalCubeAnchor318 (Ends)
open ActualTZOneAxisLocalDual318 (Params)

abbrev dim (a t s : ℕ) := Fintype.card (Coord a t s)
@[expose] def flat (a t s : ℕ) : Coord a t s≃Fin (dim a t s) := Fintype.equivFin _

@[expose] def width {a t s : ℕ} (J M : ℕ) : Coord a t s→ℕ
  | .inl _=>J
  | .inr (_,.inl _)=>M
  | .inr (_,.inr _)=>2*M+1

@[expose] def lower {a t s : ℕ} (M : ℕ) : Coord a t s→ℤ
  | .inl _=>0
  | .inr (_,.inl _)=>1
  | .inr (_,.inr _)=>-(M:ℤ)

@[expose] def lengths (a t s J M : ℕ) : Fin (dim a t s)→ℕ :=
  width J M ∘ (flat a t s).symm
@[expose] def starts (a t s M : ℕ) : Fin (dim a t s)→ℤ :=
  lower M ∘ (flat a t s).symm

abbrev GridOf (a t s J M : ℕ) := Grid (lengths a t s J M)
abbrev Ordered (a t s J M : ℕ) := Ends a J×(Fin t→Params s M)

@[expose] def digit {a t s J M : ℕ} (z : Ordered a t s J M) :
    (p : Coord a t s)→Fin (width J M p)
  | .inl (b,i)=>if b then z.1.1 i else z.1.2 i
  | .inr (r,.inl i)=>(z.2 r).1 i
  | .inr (r,.inr b)=>if b then (z.2 r).2.1 else (z.2 r).2.2

@[expose] def pack {a t s J M : ℕ} (z : Ordered a t s J M) : GridOf a t s J M :=
  fun i=>digit z ((flat a t s).symm i)

@[expose] def unflat {a t s J M : ℕ} (z : GridOf a t s J M) (p : Coord a t s) :
    Fin (width J M p) :=
  Fin.cast (by rw [lengths,Function.comp_apply,Equiv.symm_apply_apply])
    (z (flat a t s p))

@[expose] def unpack {a t s J M : ℕ} (z : GridOf a t s J M) : Ordered a t s J M :=
  ((fun i=>unflat z (.inl (true,i)),fun i=>unflat z (.inl (false,i))),
   fun r=>(fun i=>unflat z (.inr (r,.inl i)),unflat z (.inr (r,.inr true)),
     unflat z (.inr (r,.inr false))))

theorem unflat_pack {a t s J M : ℕ} (z : Ordered a t s J M) (p : Coord a t s) :
    unflat (pack z) p=digit z p := by
  apply Fin.ext
  change (digit z ((flat a t s).symm (flat a t s p))).val=(digit z p).val
  exact congrArg (fun q : Coord a t s=>(digit z q).val) ((flat a t s).symm_apply_apply p)

private theorem digit_unpack {a t s J M : ℕ} (z : GridOf a t s J M) (p : Coord a t s) :
    digit (unpack z) p=unflat z p := by
  rcases p with ⟨b,i⟩|⟨r,i|b⟩
  · cases b <;> rfl
  · rfl
  · cases b <;> rfl

/-- Exact product equivalence, without an iid uniform
difference law. It adds neither a second cyclic x nor dummy
endpoint widths to the physical grid. -/
def orderedEquiv (a t s J M : ℕ) : Ordered a t s J M≃GridOf a t s J M where
  toFun := pack
  invFun := unpack
  left_inv z := by
    rcases z with ⟨⟨u,v⟩,F⟩
    let w : Ordered a t s J M := ((u,v),F)
    change unpack (pack w)=w
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact unflat_pack w (.inl (true,i))
      · funext i
        exact unflat_pack w (.inl (false,i))
    · funext r
      apply Prod.ext
      · funext i
        exact unflat_pack w (.inr (r,.inl i))
      · apply Prod.ext
        · exact unflat_pack w (.inr (r,.inr true))
        · exact unflat_pack w (.inr (r,.inr false))
  right_inv z := by
    funext i
    apply Fin.ext
    change (digit (unpack z) ((flat a t s).symm i)).val=(z i).val
    rw [digit_unpack]
    change (z (flat a t s ((flat a t s).symm i))).val=(z i).val
    exact congrArg (fun j : Fin (dim a t s)=>(z j).val) ((flat a t s).apply_symm_apply i)

theorem lengths_min {a t s J M : ℕ} (i : Fin (dim a t s)) :
    min J M≤lengths a t s J M i := by
  unfold lengths Function.comp
  rcases (flat a t s).symm i with u|⟨r,j|b⟩
  · exact min_le_left _ _
  · exact min_le_right _ _
  · change min J M≤2*M+1
    exact (min_le_right _ _).trans (by omega)

theorem point_at {a t s J M : ℕ} (z : GridOf a t s J M) (p : Coord a t s) :
    point (lengths a t s J M) (starts a t s M) z (flat a t s p)=
      lower M p+(unflat z p).val := by
  simp only [point,starts,Function.comp_apply,Equiv.symm_apply_apply,unflat,Fin.val_cast]

/-- The mixed width has an exact physical quadratic bound using
the OLD positive fine h and the OLD 2M+1 signed endpoints. -/
theorem off_bound (a t s J M W Q n D C : ℕ) (hQ : Q*J≤n) (hC : W*M^2≤C*n)
    (A : Fin s→ℤ) (hA : ∀ i,|A i|≤(W:ℤ)*(D:ℤ)) (w : Bits a t)
    (z : Vals a t s)
    (hG : ∀ i,|z (.inl (true,i))-z (.inl (false,i))|≤(J:ℤ))
    (hH : ∀ r i,|z (.inr (r,.inl i))|≤(M:ℤ))
    (hL : ∀ r,|z (.inr (r,.inr true))-z (.inr (r,.inr false))|≤2*(M:ℤ)) :
    |off Q A w z|≤((a+2*t*s*D*C:ℕ):ℤ)*(n:ℤ) := by
  unfold off
  refine (abs_add_le _ _).trans ?_
  have h1 : |∑ i : Fin a,if w (.inl i) then (Q:ℤ)*
        (z (.inl (true,i))-z (.inl (false,i))) else 0|≤(a:ℤ)*(n:ℤ) := by
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
  have h2 (r : Fin t) : |∑ i : Fin s,A i*z (.inr (r,.inl i))|≤(s:ℤ)*(W:ℤ)*(D:ℤ)*(M:ℤ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin s,(W:ℤ)*(D:ℤ)*(M:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hA i) (hH r i) (abs_nonneg _) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  have h3 : |∑ u : Fin t,if w (.inr u) then (∑ k : Fin s,A k*z (.inr (u,.inl k)))*
      (z (.inr (u,.inr true))-z (.inr (u,.inr false))) else 0|≤
        (t:ℤ)*(2*(s:ℤ)*(D:ℤ)*(C:ℤ)*(n:ℤ)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin t,2*(s:ℤ)*(D:ℤ)*(C:ℤ)*(n:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · rw [abs_mul]
          have H := mul_le_mul (h2 i) (hL i) (abs_nonneg _) (by positivity)
          have hC' : (W:ℤ)*(M:ℤ)^2≤(C:ℤ)*(n:ℤ) := by exact_mod_cast hC
          refine H.trans ?_
          have H' := mul_le_mul_of_nonneg_left hC' (by positivity : 0≤2*(s:ℤ)*(D:ℤ))
          convert H' using 1 <;> ring
        · rw [abs_zero]; positivity
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  refine (add_le_add h1 h3).trans_eq ?_
  push_cast
  ring

end ActualTZHybridGrid318
