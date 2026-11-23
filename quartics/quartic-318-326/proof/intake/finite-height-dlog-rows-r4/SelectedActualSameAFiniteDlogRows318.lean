module
public import LinearContactSquareclass318
public import Mathlib.Tactic

/-! Mixed-characteristic arithmetic below the actual-frame comparison.
The contact list is imported literally. No residual prime, choice of
square-root sign, geometric family, or valuation inequality is assumed. -/
public section
noncomputable section

namespace SelectedActualSameAFiniteDlogRows318

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def contact (t : K) (i : Fin 4) : K :=
  t - algebraMap ℚ K (LinearContactSquareclass318.contacts i)

def product (t : K) : K := contact t 0 * contact t 1 * contact t 2 * contact t 3

def qcoeff (t dt : K) : K := dt^2 / product t

omit [Algebra ℚ K] in
/-- This is the exact clearing ratio of the pinned +11 receiver. -/
theorem clearing_ratio :
    (2765952000 : K)^2 / 1189580636160000 = 25725/4 := by norm_num

/-- These are complementary-pair coefficients: the first term d₂d₃
corresponds to contact₀ contact₁. The formulas are over the integer ring. -/
def row0 {R : Type*} [CommRing R] (d : Fin 4 → R) : R :=
  d 2*d 3 - 12*(d 1*d 3) + 11*(d 1*d 2) + 11*(d 0*d 3) -
    12*(d 0*d 2) + d 0*d 1

def row1 {R : Type*} [CommRing R] (d : Fin 4 → R) : R :=
  -74*(d 2*d 3) - 12*(d 1*d 3) + 11*(d 1*d 2) + 11*(d 0*d 3) +
    63*(d 0*d 2) + d 0*d 1

omit [CharZero K] in
theorem bezout_rows (t : K) :
    contact t 0*contact t 1 - 12*(contact t 0*contact t 2) +
      11*(contact t 0*contact t 3) + 11*(contact t 1*contact t 2) -
      12*(contact t 1*contact t 3) + contact t 2*contact t 3 = 25725*32 ∧
    -74*(contact t 0*contact t 1) - 12*(contact t 0*contact t 2) +
      11*(contact t 0*contact t 3) + 11*(contact t 1*contact t 2) +
      63*(contact t 1*contact t 3) + contact t 2*contact t 3 = 25725*t := by
  constructor <;> norm_num [contact, LinearContactSquareclass318.contacts] <;> ring

omit [Algebra ℚ K] in
private theorem pair_mul (a b c e x y dt : K)
    (hx : dt = 2*c*x) (hy : dt = 2*e*y) :
    x*y*(a*b*c*e) = (dt^2/4)*(a*b) := by
  calc
    _ = ((2*c*x)*(2*e*y)/4)*(a*b) := by ring
    _ = _ := by rw [← hx, ← hy, pow_two]

/-- No division in a residue field. The input identity is the
mixed-characteristic product rule on the original Kummer equations. -/
theorem read_rows (t dt : K) (d : Fin 4 → K) (hn : ∀ i, contact t i ≠ 0)
    (h : ∀ i, dt = 2*contact t i*d i) :
    row0 d = (25725/4:K)*32*qcoeff t dt ∧
    row1 d = (25725/4:K)*t*qcoeff t dt := by
  have hp : product t ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3)
  have h23 : d 2*d 3*product t = (dt^2/4)*(contact t 0*contact t 1) :=
    pair_mul _ _ _ _ _ _ _ (h 2) (h 3)
  have h13 : d 1*d 3*product t = (dt^2/4)*(contact t 0*contact t 2) := by
    rw [show product t = contact t 0*contact t 2*contact t 1*contact t 3 by
      unfold product
      ring]
    exact pair_mul _ _ _ _ _ _ _ (h 1) (h 3)
  have h12 : d 1*d 2*product t = (dt^2/4)*(contact t 0*contact t 3) := by
    rw [show product t = contact t 0*contact t 3*contact t 1*contact t 2 by
      unfold product
      ring]
    exact pair_mul _ _ _ _ _ _ _ (h 1) (h 2)
  have h03 : d 0*d 3*product t = (dt^2/4)*(contact t 1*contact t 2) := by
    rw [show product t = contact t 1*contact t 2*contact t 0*contact t 3 by
      unfold product
      ring]
    exact pair_mul _ _ _ _ _ _ _ (h 0) (h 3)
  have h02 : d 0*d 2*product t = (dt^2/4)*(contact t 1*contact t 3) := by
    rw [show product t = contact t 1*contact t 3*contact t 0*contact t 2 by
      unfold product
      ring]
    exact pair_mul _ _ _ _ _ _ _ (h 0) (h 2)
  have h01 : d 0*d 1*product t = (dt^2/4)*(contact t 2*contact t 3) := by
    rw [show product t = contact t 2*contact t 3*contact t 0*contact t 1 by
      unfold product
      ring]
    exact pair_mul _ _ _ _ _ _ _ (h 0) (h 1)
  constructor
  · unfold qcoeff
    rw [← mul_div_assoc]
    apply (eq_div_iff hp).mpr
    unfold row0
    linear_combination h23 - 12*h13 + 11*h12 + 11*h03 - 12*h02 + h01 +
      (dt^2/4)*(bezout_rows t).1
  · unfold qcoeff
    rw [← mul_div_assoc]
    apply (eq_div_iff hp).mpr
    unfold row1
    linear_combination -74*h23 - 12*h13 + 11*h12 + 11*h03 + 63*h02 + h01 +
      (dt^2/4)*(bezout_rows t).2

/-- Exact preimages in the original integral subring; the result cannot be
obtained merely from a comparison of rank, determinant or valuation. -/
theorem integral_pair (R : Subring K) (t dt : K) (d : Fin 4 → R)
    (hn : ∀ i, contact t i ≠ 0) (h : ∀ i, dt = 2*contact t i*(d i : K)) :
    ((row0 d : R) : K) = (25725/4:K)*32*qcoeff t dt ∧
    ((row1 d : R) : K) = (25725/4:K)*t*qcoeff t dt := by
  have hr := read_rows t dt (fun i => (d i : K)) hn h
  constructor
  · change R.subtype (row0 d) = _
    simp only [row0, map_sub, map_add, map_mul, map_ofNat]
    simpa only [row0, Subring.subtype_apply] using hr.1
  · change R.subtype (row1 d) = _
    simp only [row1, map_sub, map_add, map_mul, map_neg, map_ofNat]
    simpa only [row1, Subring.subtype_apply] using hr.2

end SelectedActualSameAFiniteDlogRows318
