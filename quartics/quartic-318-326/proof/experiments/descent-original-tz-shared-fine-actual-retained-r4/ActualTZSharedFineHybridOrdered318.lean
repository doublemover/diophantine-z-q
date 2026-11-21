module
public import ActualTZSharedFineHybridGrid318
public import ActualTZOldProductAverage318
public import ActualPointedCyclicPairing318
import all ActualTZSharedFineHybridGrid318
public section
noncomputable section
namespace ActualTZSharedFineHybridOrdered318
open scoped BigOperators
open ActualTZSharedFineHybridGrid318 ActualTZSharedFineHybridStencil318
open ActualTZExactZeroIntegerGrid318 (point)
open ActualTZOldProductAverage318 (prob permute)
open ActualPointedCyclicPairing318 (move)
variable {n a t b s J M : ℕ}

@[expose] def oldSlope (A : Fin b→Fin s→ℤ) (j : Fin b) (h : Fin s→Fin M) : ℤ :=
  ∑ k : Fin s,A j k*(((h k).val:ℤ)+1)

@[expose] def shift (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b)
    (z : Ordered a t b s J M) : ℤ :=
  (∑ i : Fin a,if w (.inl i) then (q:ℤ)*(((z.1 (true,i)).val:ℤ)-(z.1 (false,i)).val) else 0)+
  ∑ p : Fin t×Fin b,if w (.inr p) then oldSlope A p.2 (z.2 p.1).1*
    ((((z.2 p.1).2 (p.2,true)).val:ℤ)-((z.2 p.1).2 (p.2,false)).val) else 0

private theorem pack_point (z : Ordered a t b s J M) (c : Coord a t b s) :
    point (lengths a t b s J M) (starts a t b s M) (pack z) (flat a t b s c)=
      lower M c+(digit z c).val := by
  rw [point_at,unflat_pack]

theorem packed_off (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b)
    (z : Ordered a t b s J M) :
    off q A w (point (lengths a t b s J M) (starts a t b s M) (pack z) ∘ flat a t b s)=
      shift q A w z := by
  simp only [off,shift,oldSlope,Function.comp_apply,pack_point,gpos,hpos,lpos,lower,digit,
    zero_add,add_comm (1:ℤ)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

@[expose] def mixed (hn : 0<n) (q : ℕ) (A : Fin b→Fin s→ℤ)
    (F : Bits a t b→Fin n→ℝ) : ℝ :=
  prob (fun x=>prob (fun z : Ordered a t b s J M=>∏ w : Bits a t b,
    F w (move hn (shift q A w z) x)))

/-- Transport the exact ordered all-axes blocks to the unequal-width
physical grid; ONE x and ONE fine block per whole local test are
retained. No uniform distribution of endpoint differences is used. -/
theorem mixed_grid (hn : 0<n) (q : ℕ) (A : Fin b→Fin s→ℤ)
    (F : Bits a t b→Fin n→ℝ) :
    mixed (J:=J) (M:=M) hn q A F=
      prob (fun x=>prob (fun z : GridOf a t b s J M=>∏ w : Bits a t b,
        F w (move hn (off q A w (point (lengths a t b s J M)
          (starts a t b s M) z ∘ flat a t b s)) x))) := by
  unfold mixed
  congr 1
  funext x
  let G (z : GridOf a t b s J M) :=
    ∏ w : Bits a t b,F w (move hn (off q A w (point (lengths a t b s J M)
      (starts a t b s M) z ∘ flat a t b s)) x)
  calc
    _ = prob (G ∘ orderedEquiv a t b s J M) := by
      congr 1
      funext z
      change _=G (pack z)
      simp only [G,packed_off]
    _ = prob G := permute _ G
    _ = _ := rfl

end ActualTZSharedFineHybridOrdered318
