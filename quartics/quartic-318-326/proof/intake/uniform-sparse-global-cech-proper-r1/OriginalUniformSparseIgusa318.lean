module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Fixed discriminant-five sparse family. The univariate sextic is the
dehomogenization of the literal homogeneous binary form. This module proves
its classical normalized Igusa--Clebsch polynomial identities, not Torelli
or a representability theorem for the original analytic PEL family. -/

public section
namespace OriginalUniformSparseIgusa318

/-- Number multiplying (x^{i+j-r}) in the raw order-r transvectant of
 (x^i y^{n-i}) and (x^j y^{m-j}). FALLING equals zero past the boundary. -/
def falling (n k : ℕ) : ℕ :=
  (List.range k).foldr (fun t a => (n-t)*a) 1

def rawCoefficient (n m r i j : ℕ) : ℤ :=
  (List.range (r+1)).foldr (fun k a =>
    (if k%2=0 then 1 else -1 : ℤ) *
      ((Nat.choose r k * falling i (r-k) * falling (n-i) k *
        falling j k * falling (m-j) (r-k) : ℕ) : ℤ) + a) 0

def stencil (n m r l : ℕ) : List (ℕ × ℕ × ℤ) :=
  (List.range (n+1)).flatMap (fun i =>
    (List.range (m+1)).filterMap (fun j =>
      let a := rawCoefficient n m r i j
      if i+j=l+r ∧ a≠0 then some (i,j,a) else none))

section Field
variable {K : Type*} [Field K]

/-- Literal normalized transvectant coefficient, in the usual falling
factorial convention. It evaluates the native small integer stencil. -/
@[expose] def trans (n m r : ℕ) (f g : ℕ → K) (l : ℕ) : K :=
    (stencil n m r l).foldr
      (fun a acc => ((a.2.2 : ℤ) : K) * f a.1 * g a.2.1 + acc) 0 /
        ((falling n r * falling m r : ℕ) : K)

@[expose] def sparse (s t : K) : ℕ → K
  | 0 => t^2*(5-s*t)^3
  | 1 => -2*(s*t)*t*(5-s*t)^2
  | 3 => -10*(s*t)*(s*t-5)
  | 5 => -2*(s*t)*s
  | 6 => s^2
  | _ => 0

@[expose] def covQ (s t : K) := trans 6 6 4 (sparse s t) (sparse s t)
@[expose] def covD (s t : K) := trans 4 4 2 (covQ s t) (covQ s t)
@[expose] def covV (s t : K) := trans 6 4 4 (sparse s t) (covQ s t)
@[expose] def covW (s t : K) := trans 4 2 2 (covQ s t) (covV s t)
@[expose] def covU (s t : K) := trans 4 2 2 (covQ s t) (covW s t)

@[expose] def a (s t : K) := trans 6 6 6 (sparse s t) (sparse s t) 0
@[expose] def b (s t : K) := trans 4 4 4 (covQ s t) (covQ s t) 0
@[expose] def c (s t : K) := trans 4 4 4 (covQ s t) (covD s t) 0
@[expose] def e (s t : K) := trans 2 2 2 (covU s t) (covV s t) 0

@[expose] def i2 (s t : K) := -120*a s t
@[expose] def i4 (s t : K) := -720*a s t^2+6750*b s t
@[expose] def i6 (s t : K) :=
  8640*a s t^3-108000*a s t*b s t+202500*c s t
@[expose] def i10 (s t : K) :=
  -62208*a s t^5+972000*a s t^3*b s t+1620000*a s t^2*c s t
    -3037500*a s t*b s t^2-6075000*b s t*c s t-4556250*e s t
end Field

set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
private theorem tab664_0 : stencil 6 6 4 0 = [(0,4,8640), (1,3,-4320), (2,2,3456), (3,1,-4320), (4,0,8640)] := by decide +kernel
private theorem tab664_1 : stencil 6 6 4 1 = [(0,5,43200), (1,4,-8640), (2,3,1728), (3,2,1728), (4,1,-8640), (5,0,43200)] := by decide +kernel
private theorem tab664_2 : stencil 6 6 4 2 = [(0,6,129600), (2,4,-5184), (3,3,5184), (4,2,-5184), (6,0,129600)] := by decide +kernel
private theorem tab664_3 : stencil 6 6 4 3 = [(1,6,43200), (2,5,-8640), (3,4,1728), (4,3,1728), (5,2,-8640), (6,1,43200)] := by decide +kernel
private theorem tab664_4 : stencil 6 6 4 4 = [(2,6,8640), (3,5,-4320), (4,4,3456), (5,3,-4320), (6,2,8640)] := by decide +kernel
private theorem tab442_0 : stencil 4 4 2 0 = [(0,2,24), (1,1,-18), (2,0,24)] := by decide +kernel
private theorem tab442_1 : stencil 4 4 2 1 = [(0,3,72), (1,2,-12), (2,1,-12), (3,0,72)] := by decide +kernel
private theorem tab442_2 : stencil 4 4 2 2 = [(0,4,144), (1,3,18), (2,2,-24), (3,1,18), (4,0,144)] := by decide +kernel
private theorem tab442_3 : stencil 4 4 2 3 = [(1,4,72), (2,3,-12), (3,2,-12), (4,1,72)] := by decide +kernel
private theorem tab442_4 : stencil 4 4 2 4 = [(2,4,24), (3,3,-18), (4,2,24)] := by decide +kernel
private theorem tab644_0 : stencil 6 4 4 0 = [(0,4,8640), (1,3,-1440), (2,2,576), (3,1,-432), (4,0,576)] := by decide +kernel
private theorem tab644_1 : stencil 6 4 4 1 = [(1,4,2880), (2,3,-1152), (3,2,864), (4,1,-1152), (5,0,2880)] := by decide +kernel
private theorem tab644_2 : stencil 6 4 4 2 = [(2,4,576), (3,3,-432), (4,2,576), (5,1,-1440), (6,0,8640)] := by decide +kernel
private theorem tab422_0 : stencil 4 2 2 0 = [(0,2,24), (1,1,-6), (2,0,4)] := by decide +kernel
private theorem tab422_1 : stencil 4 2 2 1 = [(1,2,12), (2,1,-8), (3,0,12)] := by decide +kernel
private theorem tab422_2 : stencil 4 2 2 2 = [(2,2,4), (3,1,-6), (4,0,24)] := by decide +kernel
private theorem tab666_0 : stencil 6 6 6 0 = [(0,6,518400), (1,5,-86400), (2,4,34560), (3,3,-25920), (4,2,34560), (5,1,-86400), (6,0,518400)] := by decide +kernel
private theorem tab444_0 : stencil 4 4 4 0 = [(0,4,576), (1,3,-144), (2,2,96), (3,1,-144), (4,0,576)] := by decide +kernel
private theorem tab222_0 : stencil 2 2 2 0 = [(0,2,4), (1,1,-2), (2,0,4)] := by decide +kernel
private theorem scale222 : falling 2 2 * falling 2 2 = 4 := by decide +kernel
private theorem scale422 : falling 4 2 * falling 2 2 = 24 := by decide +kernel
private theorem scale442 : falling 4 2 * falling 4 2 = 144 := by decide +kernel
private theorem scale444 : falling 4 4 * falling 4 4 = 576 := by decide +kernel
private theorem scale644 : falling 6 4 * falling 4 4 = 8640 := by decide +kernel
private theorem scale664 : falling 6 4 * falling 6 4 = 129600 := by decide +kernel
private theorem scale666 : falling 6 6 * falling 6 6 = 518400 := by decide +kernel

section Computation
variable {K : Type*} [Field K] [CharZero K]
private theorem covQ_0 (s t : K) : covQ s t 0 = (-4 / 3)*(s)^2*(t)^3*((s*t + -5))^3 := by
  simp only [covQ, trans, tab664_0, scale664, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem covQ_1 (s t : K) : covQ s t 1 = (4 / 3)*(s)^2*(t)^3*((s*t + -5))^3 := by
  simp only [covQ, trans, tab664_1, scale664, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem covQ_2 (s t : K) : covQ s t 2 = -2*(s*t + -7)*(t)^2*(s)^2*((s*t + -5))^2 := by
  simp only [covQ, trans, tab664_2, scale664, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem covQ_3 (s t : K) : covQ s t 3 = (-4 / 3)*(t)^2*((s*t + -5))^2*(s)^3 := by
  simp only [covQ, trans, tab664_3, scale664, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem covQ_4 (s t : K) : covQ s t 4 = (-4 / 3)*(s*t + -5)*(t)^2*(s)^3 := by
  simp only [covQ, trans, tab664_4, scale664, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem covD_0 (s t : K) : covD s t 0 = (-2 / 9)*(s*t^2 + -4*s*t + -5*t + 28)*(s)^4*(t)^5*((s*t + -5))^5 := by
  simp only [covD, trans, tab442_0, scale442, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2]
  norm_num
  ring

private theorem covD_1 (s t : K) : covD s t 1 = (4 / 9)*(s*t + 4*s + -7)*(s)^4*(t)^5*((s*t + -5))^5 := by
  simp only [covD, trans, tab442_1, scale442, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3]
  norm_num
  ring

private theorem covD_2 (s t : K) : covD s t 2 = (-2 / 9)*(5*s^2*t^2 + -68*s*t + 147)*(t)^4*(s)^4*((s*t + -5))^4 := by
  simp only [covD, trans, tab442_2, scale442, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4]
  norm_num
  ring

private theorem covD_3 (s t : K) : covD s t 3 = (-4 / 9)*(s*t + 4*t + -7)*(t)^4*((s*t + -5))^4*(s)^5 := by
  simp only [covD, trans, tab442_3, scale442, List.foldr_cons, List.foldr_nil, covQ_1, covQ_2, covQ_3, covQ_4]
  norm_num
  ring

private theorem covD_4 (s t : K) : covD s t 4 = (-2 / 9)*(s^2*t + -4*s*t + -5*s + 28)*((s*t + -5))^3*(t)^4*(s)^5 := by
  simp only [covD, trans, tab442_4, scale442, List.foldr_cons, List.foldr_nil, covQ_2, covQ_3, covQ_4]
  norm_num
  ring

private theorem covV_0 (s t : K) : covV s t 0 = (-2 / 9)*(2*s + -9)*(s)^3*(t)^4*((s*t + -5))^4 := by
  simp only [covV, trans, tab644_0, scale644, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4, sparse]
  norm_num
  ring

private theorem covV_1 (s t : K) : covV s t 1 = (2 / 9)*(17*s*t + -63)*(t)^3*(s)^3*((s*t + -5))^3 := by
  simp only [covV, trans, tab644_1, scale644, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4, sparse]
  norm_num
  ring

private theorem covV_2 (s t : K) : covV s t 2 = (2 / 9)*(2*t + -9)*(t)^3*((s*t + -5))^3*(s)^4 := by
  simp only [covV, trans, tab644_2, scale644, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4, sparse]
  norm_num
  ring

private theorem covW_0 (s t : K) : covW s t 0 = (4 / 27)*(s^2*t + -17*s*t + 11*s + 63)*(s)^5*(t)^6*((s*t + -5))^6 := by
  simp only [covW, trans, tab422_0, scale422, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covV_0, covV_1, covV_2]
  norm_num
  ring

private theorem covW_1 (s t : K) : covW s t 1 = (4 / 27)*(2*s^3*t^2 + 2*s^2*t^3 + -1*s^2*t^2 + -10*s^2*t + -10*s*t^2 + -92*s*t + 441)*(t)^5*(s)^5*((s*t + -5))^5 := by
  simp only [covW, trans, tab422_1, scale422, List.foldr_cons, List.foldr_nil, covQ_1, covQ_2, covQ_3, covV_0, covV_1, covV_2]
  norm_num
  ring

private theorem covW_2 (s t : K) : covW s t 2 = (-4 / 27)*(s*t^2 + -17*s*t + 11*t + 63)*(t)^5*((s*t + -5))^5*(s)^6 := by
  simp only [covW, trans, tab422_2, scale422, List.foldr_cons, List.foldr_nil, covQ_2, covQ_3, covQ_4, covV_0, covV_1, covV_2]
  norm_num
  ring

private theorem covU_0 (s t : K) : covU s t 0 = (-4 / 81)*(3*s^2*t^2 + 2*s*t^3 + -22*s*t^2 + 62*s*t + -10*t^2 + 46*t + -329)*(t)^8*(s)^8*((s*t + -5))^8 := by
  simp only [covU, trans, tab422_0, scale422, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covW_0, covW_1, covW_2]
  norm_num
  ring

private theorem covU_1 (s t : K) : covU s t 1 = (8 / 81)*(s^4*t^3 + s^3*t^4 + 33*s^3*t^3 + -30*s^3*t^2 + -30*s^2*t^3 + -381*s^2*t^2 + 125*s^2*t + 125*s*t^2 + 1715*s*t + -3087)*(t)^7*(s)^7*((s*t + -5))^7 := by
  simp only [covU, trans, tab422_1, scale422, List.foldr_cons, List.foldr_nil, covQ_1, covQ_2, covQ_3, covW_0, covW_1, covW_2]
  norm_num
  ring

private theorem covU_2 (s t : K) : covU s t 2 = (4 / 81)*(2*s^3*t + 3*s^2*t^2 + -22*s^2*t + -10*s^2 + 62*s*t + 46*s + -329)*((s*t + -5))^7*(t)^8*(s)^8 := by
  simp only [covU, trans, tab422_2, scale422, List.foldr_cons, List.foldr_nil, covQ_2, covQ_3, covQ_4, covW_0, covW_1, covW_2]
  norm_num
  ring

private theorem a_0 (s t : K) : a s t = (-5 / 3)*(2*s*t + -3)*(t)^2*(s)^2*((s*t + -5))^2 := by
  simp only [a, trans, tab666_0, scale666, List.foldr_cons, List.foldr_nil, sparse]
  norm_num
  ring

private theorem b_0 (s t : K) : b s t = (2 / 9)*(7*s^2*t^2 + -46*s*t + 147)*(t)^4*(s)^4*((s*t + -5))^4 := by
  simp only [b, trans, tab444_0, scale444, List.foldr_cons, List.foldr_nil, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4]
  norm_num
  ring

private theorem c_0 (s t : K) : c s t = (2 / 9)*(3*s^3*t^3 + 4*s^3*t^2 + 4*s^2*t^3 + -61*s^2*t^2 + -20*s^2*t + -20*s*t^2 + 329*s*t + -343)*(t)^6*(s)^6*((s*t + -5))^6 := by
  simp only [c, trans, tab444_0, scale444, List.foldr_cons, List.foldr_nil, covD_0, covD_1, covD_2, covD_3, covD_4, covQ_0, covQ_1, covQ_2, covQ_3, covQ_4]
  norm_num
  ring

private theorem e_0 (s t : K) : e s t = (-8 / 729)*(4*s^6*t^4 + 12*s^5*t^5 + -72*s^5*t^4 + -40*s^5*t^3 + 4*s^4*t^6 + -72*s^4*t^5 + 1145*s^4*t^4 + -504*s^4*t^3 + 100*s^4*t^2 + -40*s^3*t^5 + -504*s^3*t^4 + -13920*s^3*t^3 + 8856*s^3*t^2 + 100*s^2*t^4 + 8856*s^2*t^3 + 63878*s^2*t^2 + -22680*s^2*t + -22680*s*t^2 + -160524*s*t + 194481)*(t)^10*(s)^10*((s*t + -5))^10 := by
  simp only [e, trans, tab222_0, scale222, List.foldr_cons, List.foldr_nil, covU_0, covU_1, covU_2, covV_0, covV_1, covV_2]
  norm_num
  ring

/-- Actual Igusa--Clebsch reads by the independent raw transvectants. -/
theorem reads_factored (s t : K) :
    let N := s*t
    let r := s+t
    i2 s t = 200*(2*N-3)*N^2*(N-5)^2 ∧
    i4 s t = 2500*(N-9)^2*N^4*(N-5)^4 ∧
    i6 s t = 5000*(36*r*N^2-180*r*N+75*N^3-1165*N^2+5985*N-6399)*N^6*(N-5)^6 ∧
    i10 s t = 200000*(r*N^2-5*r*N+10*N^2-90*N+216)^2*N^10*(N-5)^10 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [i2,a_0]
    ring
  · simp only [i4,a_0,b_0]
    ring
  · simp only [i6,a_0,b_0,c_0]
    ring
  · simp only [i10,a_0,b_0,c_0,e_0]
    ring

end Computation
end OriginalUniformSparseIgusa318

#print axioms OriginalUniformSparseIgusa318.reads_factored
