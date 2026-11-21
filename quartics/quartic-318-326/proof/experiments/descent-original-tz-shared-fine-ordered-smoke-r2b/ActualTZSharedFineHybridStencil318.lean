module
public import ActualTZDegreeTwoAlgebra318
public import ActualTZProbeExceptionalWheel318
public section
noncomputable section
namespace ActualTZSharedFineHybridStencil318
open scoped BigOperators
open MvPolynomial (C X eval_C eval_X)
open ActualTZDegreeTwoAlgebra318

/-- b is the active axes of ONE protected local test, t is the
number of whole local tests. All b axes in test r use the SAME
fine site (.inr (r,.inl k)). No repeated common cyclic origin. -/
abbrev Axis (a t b : ℕ) := Fin a ⊕ (Fin t×Fin b)
abbrev Bits (a t b : ℕ) := Axis a t b→Bool
abbrev Coord (a t b s : ℕ) := (Bool×Fin a) ⊕ (Fin t×(Fin s ⊕ (Fin b×Bool)))
abbrev Poly (a t b s : ℕ) := MvPolynomial (Coord a t b s) ℤ
abbrev Vals (a t b s : ℕ) := Coord a t b s→ℤ
variable {a t b s : ℕ}

@[expose] def gpos (i : Fin a) (e : Bool) : Coord a t b s :=
  .inl (e,i)
@[expose] def hpos (r : Fin t) (k : Fin s) : Coord a t b s :=
  .inr (r,.inl k)
@[expose] def lpos (r : Fin t) (j : Fin b) (e : Bool) : Coord a t b s :=
  .inr (r,.inr (j,e))

@[expose] def linear (q : ℕ) (w : Bits a t b) : Poly a t b s :=
  ∑ i : Fin a,if w (.inl i) then C (q:ℤ)*(X (gpos i true)-X (gpos i false)) else 0

@[expose] def slope (A : Fin b→Fin s→ℤ) (r : Fin t) (j : Fin b) : Poly a t b s :=
  ∑ k : Fin s,C (A j k)*X (hpos r k)

@[expose] def nonlinear (A : Fin b→Fin s→ℤ) (w : Bits a t b) : Poly a t b s :=
  ∑ p : Fin t×Fin b,if w (.inr p) then
    slope A p.1 p.2*(X (lpos p.1 p.2 true)-X (lpos p.1 p.2 false)) else 0

@[expose] def stencil (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) : Poly a t b s :=
  linear q w+nonlinear A w

@[expose] def physical (W n q : ℕ) (A : Fin b→Fin s→ℤ)
    (w v : Bits a t b) (e f : ℤ) : Poly a t b s :=
  C (W:ℤ)*(stencil q A w-stencil q A v-C ((e-f)*(n:ℤ)))

@[expose] def off (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) (z : Vals a t b s) : ℤ :=
  (∑ i : Fin a,if w (.inl i) then (q:ℤ)*(z (gpos i true)-z (gpos i false)) else 0)+
  ∑ p : Fin t×Fin b,if w (.inr p) then
    (∑ k : Fin s,A p.2 k*z (hpos p.1 k))*(z (lpos p.1 p.2 true)-z (lpos p.1 p.2 false)) else 0

theorem eval_stencil (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) (z : Vals a t b s) :
    MvPolynomial.eval z (stencil q A w)=off q A w z := by
  simp only [stencil,off,linear,nonlinear,map_add,map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [map_mul,map_sub,eval_C,eval_X,map_zero]
  · apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [slope,map_sum,map_mul,map_sub,eval_C,eval_X,map_zero]

/-- Actual same x of a wrapped cell cancels in the physical
difference. Fine labels remain shared between all axes of one
local test before and after this cancellation. -/
theorem eval_physical (W n q : ℕ) (A : Fin b→Fin s→ℤ) (w v : Bits a t b)
    (e f x c : ℤ) (z : Vals a t b s) :
    MvPolynomial.eval z (physical W n q A w v e f)=
      ((W:ℤ)*(x+off q A w z-e*n)+c)-((W:ℤ)*(x+off q A v z-f*n)+c) := by
  simp only [physical,map_mul,map_sub,eval_C,eval_stencil]
  ring

private theorem stencil_degree (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) :
    (stencil q A w).totalDegree≤2 := by
  unfold stencil
  apply addD
  · unfold linear
    apply sumD
    intro i _
    split_ifs
    · exact scaleD _ _ 2 (subD _ _ 2 ((varD _).trans (by decide)) ((varD _).trans (by decide)))
    · simp
  · unfold nonlinear
    apply sumD
    intro p _
    split_ifs
    · exact mulD _ _ 1 1 (sumD _ _ 1 (fun k _=>scaleD _ _ 1 (varD _)))
        (subD _ _ 1 (varD _) (varD _))
    · simp

theorem degree (W n q : ℕ) (A : Fin b→Fin s→ℤ) (w v : Bits a t b) (e f : ℤ) :
    (physical W n q A w v e f).totalDegree≤2 :=
  scaleD _ _ 2 (subD _ _ 2 (subD _ _ 2 (stencil_degree _ _ _) (stencil_degree _ _ _)) (constD _ 2))

end ActualTZSharedFineHybridStencil318
