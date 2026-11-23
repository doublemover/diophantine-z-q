module
public import LinearA4MixedNormCounts318
public import Mathlib.Algebra.Field.ZMod
public section
noncomputable section

/-! Actual residue selectors at the omitted collision prime. Off-diagonal
ordered forms give two independently translated Gaussian norm equations.
At a diagonal collision the first norm satisfies both translations and
the second norm is the fixed companion coordinate used for recovery. -/
namespace LinearA4CollisionBins318
open LinearA4GaussianCounts318 LinearA4MixedNormCounts318
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

@[expose] def translated (c : K) (x : Plane K) : K :=
  LinearA4GaussianCounts318.norm (x.1-c,x.2)

def shiftedEquiv (c : K) : Fibre (translated c) 0 ≃ Fibre (LinearA4GaussianCounts318.norm : Plane K → K) 0 where
  toFun x := ⟨(x.val.1-c,x.val.2),x.property⟩
  invFun x := ⟨(x.val.1+c,x.val.2),by
    change LinearA4GaussianCounts318.norm (x.val.1+c-c,x.val.2)=0
    rw [add_sub_cancel_right]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by apply Subtype.ext; apply Prod.ext <;> simp

def crossBins : Finset (Box K) :=
  Finset.univ.filter (fun z => translated 1 z.1=0 ∧ translated (-1) z.2=0)
def diagonalBins : Finset (Box K) :=
  Finset.univ.filter (fun z => translated 1 z.1=0 ∧ translated (-1) z.1=0)

theorem norm_zero_le (hchar : ringChar K≠2) (h2 : (2:K)≠0) :
    Fintype.card (Fibre (LinearA4GaussianCounts318.norm : Plane K → K) 0) ≤ 2*Fintype.card K := by
  have H := norm_count (K:=K) hchar h2 0
  unfold fibreSize at H
  rw [ite_eq_left rfl] at H
  have sz : 1≤size K := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card K)
  have hc : χ K≤1 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) with e|e
    · simp only [show χ K=1 from e,le_refl]
    · norm_num [show χ K= -1 from e]
  have hmul := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr sz)
  exact_mod_cast (show (Fintype.card (Fibre (LinearA4GaussianCounts318.norm : Plane K → K) 0):ℤ)≤2*size K by
    linarith only [H,hmul])

/-- Exact independent translated fibres. In particular the medium-CRT
intersection has at most 4p² bins, with no hypothesis about joint primes. -/
theorem cross_card_le (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    (crossBins (K:=K)).card ≤ 4*(Fintype.card K)^2 := by
  let e : {z : Box K // translated 1 z.1=0 ∧ translated (-1) z.2=0} ≃
      Fibre (translated (1:K)) 0 × Fibre (translated (-1:K)) 0 :=
    ⟨fun z => (⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩),
     fun z => ⟨(z.1.val,z.2.val),z.1.property,z.2.property⟩,
     fun _ => rfl,fun _ => rfl⟩
  have hshift (c : K) : Fintype.card (Fibre (translated c) 0) ≤ 2*Fintype.card K :=
    (Fintype.card_congr (shiftedEquiv c)).le.trans (norm_zero_le hp h2)
  calc
    (crossBins (K:=K)).card =
        Fintype.card (Fibre (translated (1:K)) 0) *
          Fintype.card (Fibre (translated (-1:K)) 0) := by
      have hc := Fintype.card_congr e
      rw [Fintype.card_subtype,Fintype.card_prod] at hc
      exact hc
    _ ≤ (2*Fintype.card K)*(2*Fintype.card K) :=
      Nat.mul_le_mul (hshift 1) (hshift (-1))
    _ = _ := by ring

omit [Fintype K] [DecidableEq K] in
theorem diagonal_first (h2 : (2:K)≠0) (z : Plane K) :
    translated 1 z=0 ∧ translated (-1) z=0 ↔ z.1=0 ∧ z.2^2=(-1:K) := by
  constructor
  · rintro ⟨h₁,h₂⟩
    change (z.1-1)^2+z.2^2=0 at h₁
    change (z.1-(-1))^2+z.2^2=0 at h₂
    have he : (4:K)*z.1=0 := by linear_combination h₂-h₁
    have h4 : (4:K)≠0 := by
      rw [show (4:K)=2^2 by norm_num]
      exact pow_ne_zero _ h2
    have hn : z.1=0 := (mul_eq_zero.mp he).resolve_left h4
    refine ⟨hn,?_⟩
    rw [hn] at h₁
    linear_combination h₁
  · rintro ⟨ha,hb⟩
    constructor
    · change (z.1-1)^2+z.2^2=0
      rw [ha,hb]
      ring
    · change (z.1-(-1))^2+z.2^2=0
      rw [ha,hb]
      ring

/-- The same-position opposite-sign collision gives at most two values
of its imaginary coordinate, with an unrestricted companion norm pair. -/
theorem diagonal_card_le (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    (diagonalBins (K:=K)).card ≤ 2*(Fintype.card K)^2 := by
  let e : {z : Box K // translated 1 z.1=0 ∧ translated (-1) z.1=0} ≃
      {b : K // b^2=(-1:K)} × Plane K :=
    ⟨fun z => (⟨z.val.1.2,((diagonal_first h2 z.val.1).mp z.property).2⟩,z.val.2),
     fun z => ⟨((0,z.1.val),z.2),(diagonal_first h2 _).mpr ⟨rfl,z.1.property⟩⟩,
     (by intro z; apply Subtype.ext; apply Prod.ext
         · apply Prod.ext
           · exact ((diagonal_first h2 z.val.1).mp z.property).1.symm
           · rfl
         · rfl),
     fun _ => rfl⟩
  have H := char_root_count (K:=K) hp (-1)
  have hb : Fintype.card {b : K // b^2=(-1:K)}≤2 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) with r|r
    · rw [r] at H
      exact_mod_cast (show (Fintype.card {b : K // b^2=(-1:K)}:ℤ)≤2 by linarith)
    · rw [r] at H
      exact_mod_cast (show (Fintype.card {b : K // b^2=(-1:K)}:ℤ)≤2 by linarith)
  have hc := Fintype.card_congr e
  rw [Fintype.card_subtype,Fintype.card_prod,Fintype.card_prod] at hc
  unfold diagonalBins
  rw [hc,pow_two]
  exact Nat.mul_le_mul_right _ hb

section Integers
variable (p : ℕ) [Fact p.Prime]
def reducePlane (x : ℤ × ℤ) : Plane (ZMod p) := ((x.1:ZMod p),(x.2:ZMod p))

theorem translated_reading (c : ℤ) (x : ℤ × ℤ) :
    translated (c:ZMod p) (reducePlane p x)
      = (((x.1-c)^2+x.2^2:ℤ):ZMod p) := by
  simp [translated,reducePlane,LinearA4GaussianCounts318.norm]

theorem cross_mem_of_dvd (x y : ℤ × ℤ)
    (hx : (p:ℤ)∣(x.1-1)^2+x.2^2) (hy : (p:ℤ)∣(y.1+1)^2+y.2^2) :
    (reducePlane p x,reducePlane p y)∈crossBins := by
  unfold crossBins
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  constructor
  · rw [← Int.cast_one,translated_reading]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hx
  · rw [← Int.cast_one,← Int.cast_neg,translated_reading]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
    exact (by simpa only [sub_neg_eq_add] using hy)

theorem diagonal_mem_of_dvd (x y : ℤ × ℤ)
    (hx : (p:ℤ)∣(x.1-1)^2+x.2^2) (hy : (p:ℤ)∣(x.1+1)^2+x.2^2) :
    (reducePlane p x,reducePlane p y)∈diagonalBins := by
  rcases Finset.mem_filter.mp (cross_mem_of_dvd p x x hx hy) with ⟨_,h⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
end Integers

end LinearA4CollisionBins318
