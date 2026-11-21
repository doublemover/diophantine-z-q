module
public import ActualTZSharedFineHybridOffsetCap318
public import ActualTZExactZeroIntegerGrid318
import all ActualTZExactZeroIntegerGrid318
public section
noncomputable section
namespace ActualTZSharedFineHybridGrid318
open scoped BigOperators
open ActualTZSharedFineHybridStencil318
open ActualTZExactZeroIntegerGrid318

abbrev dim (a t b s : ℕ) := Fintype.card (Coord a t b s)

theorem dimension (a t b s : ℕ) : dim a t b s=2*a+t*(s+2*b) := by
  simp only [dim,Coord,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  ring

@[expose] def flat (a t b s : ℕ) : Coord a t b s≃Fin (dim a t b s) :=
  Fintype.equivFin _

@[expose] def width {a t b s : ℕ} (J M : ℕ) : Coord a t b s→ℕ
  | .inl _ => J
  | .inr (_,.inl _) => M
  | .inr (_,.inr _) => 2*M+1

@[expose] def lower {a t b s : ℕ} (M : ℕ) : Coord a t b s→ℤ
  | .inl _ => 0
  | .inr (_,.inl _) => 1
  | .inr (_,.inr _) => -(M:ℤ)

@[expose] def lengths (a t b s J M : ℕ) : Fin (dim a t b s)→ℕ :=
  width J M ∘ (flat a t b s).symm
@[expose] def starts (a t b s M : ℕ) : Fin (dim a t b s)→ℤ :=
  lower M ∘ (flat a t b s).symm

abbrev GridOf (a t b s J M : ℕ) := Grid (lengths a t b s J M)
abbrev Block (b s M : ℕ) := (Fin s→Fin M)×((Fin b×Bool)→Fin (2*M+1))
abbrev Ordered (a t b s J M : ℕ) :=
  ((Bool×Fin a)→Fin J)×(Fin t→Block b s M)

theorem ordered_card (a t b s J M : ℕ) :
    Fintype.card (Ordered a t b s J M)=J^(2*a)*(M^s*(2*M+1)^(2*b))^t := by
  simp only [Ordered,Block,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [Nat.mul_comm b 2]

@[expose] def digit {a t b s J M : ℕ} (z : Ordered a t b s J M) :
    (c : Coord a t b s)→Fin (width J M c)
  | .inl p => z.1 p
  | .inr (r,.inl k) => (z.2 r).1 k
  | .inr (r,.inr j) => (z.2 r).2 j

@[expose] def pack {a t b s J M : ℕ} (z : Ordered a t b s J M) : GridOf a t b s J M :=
  fun i=>digit z ((flat a t b s).symm i)

@[expose] def unflat {a t b s J M : ℕ} (z : GridOf a t b s J M) (c : Coord a t b s) :
    Fin (width J M c) :=
  Fin.cast (by rw [lengths,Function.comp_apply,Equiv.symm_apply_apply])
    (z (flat a t b s c))

@[expose] def unpack {a t b s J M : ℕ} (z : GridOf a t b s J M) : Ordered a t b s J M :=
  (fun p=>unflat z (.inl p),
    fun r=>(fun k=>unflat z (.inr (r,.inl k)),fun j=>unflat z (.inr (r,.inr j))))

theorem unflat_pack {a t b s J M : ℕ} (z : Ordered a t b s J M) (c : Coord a t b s) :
    unflat (pack z) c=digit z c := by
  apply Fin.ext
  change (digit z ((flat a t b s).symm (flat a t b s c))).val=(digit z c).val
  exact congrArg (fun q : Coord a t b s=>(digit z q).val) ((flat a t b s).symm_apply_apply c)

private theorem digit_unpack {a t b s J M : ℕ} (z : GridOf a t b s J M) (c : Coord a t b s) :
    digit (unpack z) c=unflat z c := by
  rcases c with p|⟨r,k|j⟩ <;> rfl

/-- These are the exact old ordered all-endpoint blocks. There
is one fine array per r, not a separate array per local j. -/
def orderedEquiv (a t b s J M : ℕ) : Ordered a t b s J M≃GridOf a t b s J M where
  toFun := pack
  invFun := unpack
  left_inv z := by
    apply Prod.ext
    · funext p
      exact unflat_pack z (.inl p)
    · funext r
      apply Prod.ext
      · funext k
        exact unflat_pack z (.inr (r,.inl k))
      · funext j
        exact unflat_pack z (.inr (r,.inr j))
  right_inv z := by
    funext i
    apply Fin.ext
    change (digit (unpack z) ((flat a t b s).symm i)).val=(z i).val
    rw [digit_unpack]
    change (z (flat a t b s ((flat a t b s).symm i))).val=(z i).val
    exact congrArg (fun q : Fin (dim a t b s)=>(z q).val) ((flat a t b s).apply_symm_apply i)

theorem lengths_min {a t b s J M : ℕ} (i : Fin (dim a t b s)) :
    min J M≤lengths a t b s J M i := by
  unfold lengths Function.comp
  rcases (flat a t b s).symm i with u|⟨r,k|j⟩
  · exact min_le_left _ _
  · exact min_le_right _ _
  · change min J M≤2*M+1
    exact (min_le_right _ _).trans (by omega)

theorem point_at {a t b s J M : ℕ} (z : GridOf a t b s J M) (u : Coord a t b s) :
    point (lengths a t b s J M) (starts a t b s M) z (flat a t b s u)=
      lower M u+(unflat z u).val := by
  simp only [point,starts,Function.comp_apply,Equiv.symm_apply_apply,unflat,Fin.val_cast]

end ActualTZSharedFineHybridGrid318
