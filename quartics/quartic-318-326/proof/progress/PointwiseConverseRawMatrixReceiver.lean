module
public import PointwiseConverseInnerStabilization
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open Filter

namespace PointwiseConverseRawMatrixReceiver

/-- Fixed, ordered matrix slots in one outer instance. The slots may encode
degree-one and degree-two cochain tests, or comparison maps. Padding and
the choice of the retained bases are inputs to this receiver. -/
structure Shape where
  slots : ℕ
  rows : Fin slots → ℕ
  cols : Fin slots → ℕ

def modulus (r : ℕ) : ℕ := (2 : ℕ) ^ r

/-- Each entry is the coefficient vector of length `r` over `ZMod (2^r)`. -/
abbrev Packet (S : Shape) (r : ℕ) : Type :=
  (m : Fin S.slots) → Fin (S.rows m) → Fin (S.cols m) → Fin r → ZMod (modulus r)

/-- Unreduced, integer coefficient lifts for the same fixed matrices.
Only degrees below the requested precision will be read. -/
abbrev RawPacket (S : Shape) : Type :=
  (m : Fin S.slots) → Fin (S.rows m) → Fin (S.cols m) → ℕ → ℤ

instance (S : Shape) (r : ℕ) : Finite (Packet S r) := by
  let : NeZero (modulus r) := ⟨pow_ne_zero r (by decide : (2 : ℕ) ≠ 0)⟩
  dsimp only [Packet]
  infer_instance

theorem modulus_dvd {r s : ℕ} (h : r ≤ s) : modulus r ∣ modulus s :=
  pow_dvd_pow (2 : ℕ) h

def residueReduce {r s : ℕ} (h : r ≤ s) : ZMod (modulus s) →+* ZMod (modulus r) :=
  ZMod.castHom (modulus_dvd h) (ZMod (modulus r))

/-- Retain low degrees and then lower the integer modulus. -/
def reduce (S : Shape) {r s : ℕ} (h : r ≤ s) (A : Packet S s) : Packet S r :=
  fun m a b d => residueReduce h (A m a b ⟨d.val, lt_of_lt_of_le d.isLt h⟩)

theorem reduce_refl (S : Shape) (r : ℕ) (A : Packet S r) :
    reduce S (le_refl r) A = A := by
  funext m a b d
  have h : residueReduce (le_refl r) = RingHom.id (ZMod (modulus r)) :=
    Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (modulus r) →+* ZMod (modulus r) => f (A m a b d)) h

theorem reduce_comp (S : Shape) {r s q : ℕ} (h : r ≤ s) (k : s ≤ q)
    (A : Packet S q) : reduce S h (reduce S k A) = reduce S (h.trans k) A := by
  funext m a b d
  have hc : (residueReduce h).comp (residueReduce k) = residueReduce (h.trans k) :=
    ZMod.castHom_comp (modulus_dvd h) (modulus_dvd k)
  exact congrArg (fun f : ZMod (modulus q) →+* ZMod (modulus r) =>
    f (A m a b ⟨d.val, lt_of_lt_of_le d.isLt (h.trans k)⟩)) hc

def evaluate (S : Shape) (r : ℕ) (A : RawPacket S) : Packet S r :=
  fun m a b d => (A m a b d.val : ZMod (modulus r))

theorem reduce_evaluate (S : Shape) {r s : ℕ} (h : r ≤ s) (A : RawPacket S) :
    reduce S h (evaluate S s A) = evaluate S r A := by
  funext m a b d
  exact map_intCast (residueReduce h) (A m a b d.val)

/-- Exact test for two lifted raw packets to represent the same retained
evaluation. It is a condition on every basis entry, not just on cycles. -/
theorem evaluate_eq_iff (S : Shape) (r : ℕ) (A B : RawPacket S) :
    evaluate S r A = evaluate S r B ↔
      ∀ (m : Fin S.slots) (a : Fin (S.rows m)) (b : Fin (S.cols m)) (d : Fin r),
        (modulus r : ℤ) ∣ B m a b d.val - A m a b d.val := by
  constructor
  · intro h m a b d
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (modulus r)).mp
      (congrFun (congrFun (congrFun (congrFun h m) a) b) d)
  · intro h
    funext m a b d
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (modulus r)).mpr (h m a b d)

/-- A precision-`r` row is extracted from each stage independently.
No relation between the underlying stages (e.g. actual primes) is assumed. -/
def row (S : Shape) (stage : (i : ℕ) → Packet S i) (r i : ℕ) : Packet S r :=
  if h : r ≤ i then reduce S h (stage i) else fun _ _ _ _ => 0

theorem reduce_row_on_tail (S : Shape) (stage : (i : ℕ) → Packet S i)
    (r i : ℕ) (h : r + 1 ≤ i) :
    reduce S (Nat.le_succ r) (row S stage (r + 1) i) = row S stage r i := by
  have h' : r ≤ i := (Nat.le_succ r).trans h
  simp only [row, dite_eq_left h, dite_eq_left h']
  exact reduce_comp S (Nat.le_succ r) h (stage i)

/-- A single cofinal ultrafilter gives compatible values at all finite
precisions. The family of original stage packets need not itself commute
as a tower: both reductions in the tail proof start from the same stage. -/
theorem existsUnique_compatible_packets (S : Shape) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (stage : (i : ℕ) → Packet S i) :
    ∃! value : (r : ℕ) → Packet S r,
      (∀ r, ∀ᶠ i in (U : Filter ℕ), row S stage r i = value r) ∧
        (∀ r, reduce S (Nat.le_succ r) (value (r + 1)) = value r) :=
  PointwiseConverseInnerStabilization.existsUnique_compatible_on_tails U hU
    (Packet S) (fun r => reduce S (Nat.le_succ r)) (row S stage)
    (reduce_row_on_tail S stage)

/-- Actual matching at each full retained stage gives matching stabilized
matrices. This accepts equality already proved in the actual finite Artin
model; it does not manufacture a matching arithmetic representative. -/
theorem stabilized_rows_eq (S : Shape) (U : Ultrafilter ℕ)
    (left right : (i : ℕ) → Packet S i)
    (h : ∀ᶠ i in (U : Filter ℕ), left i = right i) (r : ℕ) :
    PointwiseConverseInnerStabilization.stabilizedValue U (row S left r) =
      PointwiseConverseInnerStabilization.stabilizedValue U (row S right r) := by
  apply PointwiseConverseInnerStabilization.stabilizedValue_congr U
  exact h.mono (fun i hi => by unfold row; rw [hi])

end PointwiseConverseRawMatrixReceiver
