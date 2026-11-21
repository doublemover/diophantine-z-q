module
public import ActualTZHybridGrid318
import all ActualTZHybridGrid318
import all ActualTZFiniteBoxes318
public section
noncomputable section
namespace ActualTZHybridOrderedMeaning318
open scoped BigOperators
open ActualTZHybridGrid318 ActualTZHybridGlobalLocalStencil318 ActualTZExactZeroIntegerGrid318
open ActualTZGlobalCubeAnchor318 (Ends)
open ActualTZOneAxisLocalDual318 (Params slope step)
open ActualTZOldProductAverage318 ActualPointedCyclicPairing318
open ActualTZFiniteBoxes318 (Vertex)
variable {n a t s J M : ℕ}

@[expose] def exactShift (Q : ℕ) (A : Fin s→ℤ) (w : Bits a t)
    (z : Ordered a t s J M) : ℤ :=
  ActualTZGlobalCubeAnchor318.off Q z.1 (w ∘ Sum.inl)+
    ∑ i : Fin t,if w (.inr i) then step A (z.2 i) else 0

/-- Original h_j+1 and signed endpoints give the ACTUAL hybrid
shift; signed endpoint starts cancel even when p or x wraps. -/
theorem packed_off (Q : ℕ) (A : Fin s→ℤ) (w : Bits a t) (z : Ordered a t s J M) :
    off Q A w (point (lengths a t s J M) (starts a t s M) (pack z) ∘ flat a t s)=
      exactShift Q A w z := by
  have hG (b : Bool) (i : Fin a) :
      point (lengths a t s J M) (starts a t s M) (pack z) (flat a t s (.inl (b,i)))=
        (if b then (z.1.1 i).val else (z.1.2 i).val) := by
    rw [point_at,unflat_pack]
    cases b <;> simp [lower,digit]
  have hH (r : Fin t) (i : Fin s) :
      point (lengths a t s J M) (starts a t s M) (pack z) (flat a t s (.inr (r,.inl i)))=
        ((z.2 r).1 i).val+(1:ℤ) := by
    rw [point_at,unflat_pack]
    simp [lower,digit,add_comm]
  have hL (r : Fin t) (b : Bool) :
      point (lengths a t s J M) (starts a t s M) (pack z) (flat a t s (.inr (r,.inr b)))=
        (if b then (z.2 r).2.1.val else (z.2 r).2.2.val)-(M:ℤ) := by
    rw [point_at,unflat_pack]
    cases b <;> simp [lower,digit] <;> ring
  simp only [off,exactShift,ActualTZGlobalCubeAnchor318.off,ActualTZFiniteBoxes318.shift,
    Function.comp_apply,hG,hH,hL,if_true,if_false,step,slope]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

@[expose] def mixed (hn : 0<n) (Q : ℕ) (A : Fin s→ℤ)
    (F : Bits a t→Fin n→ℝ) : ℝ :=
  prob (fun x=>prob (fun z : Ordered a t s J M=>∏ w : Bits a t,
    F w (move hn (exactShift Q A w z) x)))

/-- The exact finite chamber mean with both unequal widths.
Products have one shared x. This transports only the physical
grid indices, never the signed or bounded functions. -/
theorem grid_mixed (hn : 0<n) (Q : ℕ) (A : Fin s→ℤ)
    (F : Bits a t→Fin n→ℝ) :
    mixed (J:=J) (M:=M) hn Q A F=
      prob (fun x=>prob (fun z : GridOf a t s J M=>∏ w : Bits a t,
        F w (move hn (off Q A w (point (lengths a t s J M) (starts a t s M) z ∘ flat a t s)) x))) := by
  unfold mixed
  congr 1
  funext x
  let G (z : GridOf a t s J M) :=
    ∏ w : Bits a t,F w (move hn (off Q A w (point (lengths a t s J M)
      (starts a t s M) z ∘ flat a t s)) x)
  calc
    _ = prob (G ∘ orderedEquiv a t s J M) := by
      congr 1
      funext z
      change _=G (pack z)
      simp only [G,packed_off]
    _ = prob G := permute _ G
    _ = _ := rfl

end ActualTZHybridOrderedMeaning318
