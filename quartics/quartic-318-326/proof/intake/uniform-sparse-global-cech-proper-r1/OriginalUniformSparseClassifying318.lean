module
public import OriginalUniformSparseIgusa318
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-! Exact weight join from the literal original normalized Nagano coordinates
through the universal Elkies--Kumar map to the actual sparse family. Neither
an equality of moduli functors nor the relative analytic exponential is
asserted here. -/

public section
namespace OriginalUniformSparseClassifying318

open OriginalUniformSparseIgusa318 (i2 i4 i6 i10 reads_factored)

variable {K : Type*} [Field K]

@[expose] def ek2 (g : K) : K := 6*(4*g+1)
@[expose] def ek4 (g : K) : K := 9*g^2
@[expose] def ek6 (g h : K) : K := 9*(4*h+9*g^3+2*g^2)
@[expose] def ek10 (h : K) : K := 4*h^2

@[expose] def nag2 (a b c : K) : K := 150*b^2/c-20*a
@[expose] def nag4 (a : K) : K := 25*a^2/4
@[expose] def nag6 (a b c : K) : K :=
  (27*(-125*a^3/216+5*b/8)+nag2 a b c*nag4 a)/3
@[expose] def nag10 (c : K) : K := c/256

@[expose] def ell (b c : K) : K := 25*b^2/c
@[expose] def groundG (a b c : K) : K := -(a*c)/(30*b^2)
@[expose] def groundH (b c : K) : K := c^3/(100000*b^5)
@[expose] def groundN (a b c : K) : K := 30*groundG a b c+9
@[expose] def sparseM (g h N : K) : K :=
  (6250*h-9*(250*g^2+75*g+6))/(N*(15*g+2))
@[expose] def readG (N : K) : K := (N-9)/30
@[expose] def readH (N m g : K) : K :=
  (m*N*(15*g+2)+9*(250*g^2+75*g+6))/6250
@[expose] def wt (N : K) : K := 500*N^2*(N-5)^2

variable [CharZero K]

/-- Full weighted comparison from the actual binary form, before selecting a
square root or a point on the QM curve. -/
theorem via_EK (s t : K) :
    let N := s*t
    let g := readG N
    let h := readH N ((s+t)/2) g
    i2 s t = wt N*ek2 g ∧ i4 s t = (wt N)^2*ek4 g ∧
    i6 s t = (wt N)^3*ek6 g h ∧ i10 s t = (wt N)^5*ek10 h := by
  obtain ⟨a,b,c,d⟩ := reads_factored s t
  dsimp only at a b c d ⊢
  rw [a,b,c,d]
  unfold wt ek2 ek4 ek6 ek10 readG readH
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The Nagano tuple is the same EK map in its own exact weighted frame.
Here b,c are the scaled Nagano coordinates, not the unscaled theta pair. -/
theorem via_Nagano (a b c : K) (hb : b ≠ 0) (hc : c ≠ 0) :
    let g := groundG a b c
    let h := groundH b c
    let L := ell b c
    nag2 a b c = L*ek2 g ∧ nag4 a = L^2*ek4 g ∧
    nag6 a b c = L^3*ek6 g h ∧ nag10 c = L^5*ek10 h := by
  dsimp only
  unfold ell groundG groundH nag10 nag6 nag4 nag2 ek2 ek4 ek6 ek10
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals field_simp
  all_goals ring

/-- The single original choice of R gives the actual sparse class over the
same normalized Nagano base field, independently of either component sign.
The two explicit nonzero multipliers give weighted projective equality;
no generic inverse of an unordered list of pointwise invariants is used. -/
theorem classifying (a b c R : K) (hb : b ≠ 0) (hc : c ≠ 0)
    (hN : groundN a b c ≠ 0) (h5 : groundN a b c-5 ≠ 0)
    (hV : 15*groundG a b c+2 ≠ 0)
    (hR : R^2 = (sparseM (groundG a b c) (groundH b c) (groundN a b c))^2 -
      groundN a b c) :
    let N := groundN a b c
    let m := sparseM (groundG a b c) (groundH b c) N
    let s := m+R
    let t := m-R
    let L := ell b c
    let W := wt N
    L ≠ 0 ∧ W ≠ 0 ∧
    L*i2 s t = W*nag2 a b c ∧ L^2*i4 s t = W^2*nag4 a ∧
    L^3*i6 s t = W^3*nag6 a b c ∧ L^5*i10 s t = W^5*nag10 c := by
  let N := groundN a b c
  let g := groundG a b c
  let h := groundH b c
  let m := sparseM g h N
  let s := m+R
  let t := m-R
  have hprod : s*t=N := by
    change (m+R)*(m-R)=N
    change R^2=m^2-N at hR
    linear_combination -hR
  have hsum : (s+t)/2=m := by
    change ((m+R)+(m-R))/2=m
    ring
  have hg : readG N=g := by
    change (30*g+9-9)/30=g
    ring
  have hh : readH N m g=h := by
    have hm : m*(N*(15*g+2))=6250*h-9*(250*g^2+75*g+6) := by
      unfold m sparseM
      exact div_mul_cancel₀ _ (mul_ne_zero hN hV)
    unfold readH
    apply (div_eq_iff (by norm_num : (6250:K) ≠ 0)).2
    linear_combination hm
  obtain ⟨u2,u4,u6,u10⟩ := via_EK s t
  simp only [hprod, hsum, hg, hh] at u2 u4 u6 u10
  obtain ⟨w2,w4,w6,w10⟩ := via_Nagano a b c hb hc
  dsimp only at w2 w4 w6 w10 ⊢
  change ell b c ≠ 0 ∧ wt N ≠ 0 ∧
    ell b c*i2 s t = wt N*nag2 a b c ∧ (ell b c)^2*i4 s t = (wt N)^2*nag4 a ∧
    (ell b c)^3*i6 s t = (wt N)^3*nag6 a b c ∧
    (ell b c)^5*i10 s t = (wt N)^5*nag10 c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hb)) hc
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hN)) (pow_ne_zero _ h5)
  · rw [u2,w2]
    ring
  · rw [u4,w4]
    ring
  · rw [u6,w6]
    ring
  · rw [u10,w10]
    ring

/-- The actual sparse discriminant reading is nonzero wherever this
original normalized classifying chart is valid. -/
theorem nonzero_i10 (a b c R : K) (hb : b ≠ 0) (hc : c ≠ 0)
    (hN : groundN a b c ≠ 0) (h5 : groundN a b c-5 ≠ 0)
    (hV : 15*groundG a b c+2 ≠ 0)
    (hR : R^2 = (sparseM (groundG a b c) (groundH b c) (groundN a b c))^2 -
      groundN a b c) :
    let m := sparseM (groundG a b c) (groundH b c) (groundN a b c)
    i10 (m+R) (m-R) ≠ 0 := by
  obtain ⟨_,hw,_,_,_,hd⟩ := classifying a b c R hb hc hN h5 hV hR
  dsimp only at hw hd ⊢
  intro hz
  rw [hz,mul_zero] at hd
  exact (mul_ne_zero (pow_ne_zero 5 hw)
    (div_ne_zero hc (by norm_num : (256 : K) ≠ 0))) hd.symm

end OriginalUniformSparseClassifying318

#print axioms OriginalUniformSparseClassifying318.classifying
#print axioms OriginalUniformSparseClassifying318.nonzero_i10
