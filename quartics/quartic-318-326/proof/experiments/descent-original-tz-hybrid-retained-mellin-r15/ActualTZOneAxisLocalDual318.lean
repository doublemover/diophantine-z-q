module
public import ActualTZFiniteBoxes318
public import ActualTZWeightedAxisSplit318
import all ActualTZFiniteBoxes318
public section
noncomputable section
namespace ActualTZOneAxisLocalDual318
open scoped BigOperators
open ActualTZFiniteBoxes318 ActualPointedCyclicPairing318
open ActualTZOldProductAverage318 ActualTZWeightedAxisSplit318

variable {n s M : ℕ}
abbrev Fine (s M : ℕ) := Fin s→Fin M
abbrev Digit (M : ℕ) := Fin (2*M+1)
abbrev Pair (M : ℕ) := Digit M×Digit M
abbrev Params (s M : ℕ) := Fine s M×Pair M

@[expose] def slope (A : Fin s→ℤ) (h : Fine s M) : ℤ :=
  ∑ i : Fin s,A i*(((h i).val:ℤ)+1)

@[expose] def step (A : Fin s→ℤ) (z : Params s M) : ℤ :=
  slope A z.1*((z.2.1.val:ℤ)-(z.2.2.val:ℤ))

@[expose] def action (A : Fin s→ℤ) (hn : 0<n) (f : Fin n→ℝ) (x : Fin n) : ℝ :=
  prob (fun z : Params s M=>f (move hn (step A z) x))

private def swap (s M : ℕ) : Params s M≃Params s M :=
  Equiv.prodCongr (Equiv.refl (Fine s M)) (Equiv.prodComm (Digit M) (Digit M))

private theorem step_swap (A : Fin s→ℤ) (z : Params s M) :
    step A (swap s M z)=-step A z := by
  rcases z with ⟨h,u,v⟩
  change slope A h*((v.val:ℤ)-(u.val:ℤ))=- (slope A h*((u.val:ℤ)-(v.val:ℤ)))
  ring

theorem prob_swap {X Y : Type*} [Fintype X] [Fintype Y] (F : X→Y→ℝ) :
    prob (fun x=>prob (F x))=prob (fun y=>prob (fun x=>F x y)) := by
  rw [nested,nested]
  exact permute (Equiv.prodComm X Y) (fun z : Y×X=>F z.2 z.1)

private theorem cyclic_adjoint (hn : 0<n) (d : ℤ) (f g : Fin n→ℝ) :
    prob (fun x=>f x*g (move hn d x))=prob (fun x=>g x*f (move hn (-d) x)) := by
  let F (x : Fin n) := f x*g (move hn d x)
  let e := translation hn (-d)
  calc
    _ = prob F := rfl
    _ = prob (F ∘ e) := (permute e F).symm
    _ = _ := by
      congr 1
      funext x
      simp only [F,e,Function.comp_apply,translation_apply,move_add,neg_add_cancel,move_zero,mul_comm]

/-- Real self-adjoint local dual with the exact conserved x;
the sign change comes from swapping the two ordered endpoints. -/
theorem self_adjoint (A : Fin s→ℤ) (hn : 0<n) (f g : Fin n→ℝ) :
    prob (fun x=>f x*action (M:=M) A hn g x)=
      prob (fun x=>g x*action (M:=M) A hn f x) := by
  simp only [action,←prob_left]
  rw [prob_swap,prob_swap (fun x z=>g x*f (move hn (step A z) x))]
  let H (z : Params s M) := prob (fun x=>g x*f (move hn (step A z) x))
  calc
    _ = prob (H ∘ swap s M) := by
      congr 1
      funext z
      simpa only [H,Function.comp_apply,step_swap] using cyclic_adjoint hn (step A z) f g
    _ = _ := permute (swap s M) H

@[expose] def localProbe (A : Fin s→ℤ) (hn : 0<n) (e : Fin n→ℝ) (ε : ℝ) : Prop :=
  ∀ g : Fin n→ℝ,(∀ x,|g x|≤1)→
    |prob (fun x=>e x*action (M:=M) A hn g x)|≤ε

theorem dual_L1 (A : Fin s→ℤ) (hn : 0<n) (e : Fin n→ℝ) (ε : ℝ)
    (h : localProbe (M:=M) A hn e ε) :
    prob (fun x=>|action (M:=M) A hn e x|)≤ε := by
  let g (x : Fin n) := if 0≤action (M:=M) A hn e x then (1:ℝ) else -1
  have hg (x : Fin n) : |g x|≤1 := by unfold g; split <;> norm_num
  have hF (x : Fin n) : g x*action (M:=M) A hn e x=|action (M:=M) A hn e x| := by
    unfold g
    split
    · rename_i hp
      rw [one_mul,abs_of_nonneg hp]
    · rename_i hp
      rw [neg_one_mul,abs_of_neg (lt_of_not_ge hp)]
  have H := h g hg
  rw [self_adjoint A,show (fun x=>g x*action (M:=M) A hn e x)=
    (fun x=>|action (M:=M) A hn e x|) from funext hF] at H
  exact (le_abs_self _).trans H

private def finOne (X : Type*) : (Fin 1→X)≃X where
  toFun f := f 0
  invFun x _ := x
  left_inv f := funext (fun i=>by rw [Fin.eq_zero i])
  right_inv _ := rfl

private theorem one_slice (hn : 0<n) (d : ℤ) (f : Fin n→ℝ) :
    boxPower n 1 (2*M+1) hn (fun _=>d) f=
      prob (fun z : Fin n×Pair M=>f z.1*f (move hn (d*((z.2.1.val:ℤ)-(z.2.2.val:ℤ))) z.1)) := by
  let j := finOne (Digit M)
  let v := finOne Bool
  let E : CubeArgs n 1 (2*M+1)≃Fin n×Pair M :=
    Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.prodCongr j j)
  let F (z : Fin n×Pair M) := f z.1*f (move hn (d*((z.2.1.val:ℤ)-(z.2.2.val:ℤ))) z.1)
  have hProd (z : CubeArgs n 1 (2*M+1)) :
      (∏ ω : Vertex 1,f (move hn (ActualTZFiniteBoxes318.shift (fun _=>d) z.2.1 z.2.2 ω) z.1))=F (E z) := by
    let Y (b : Bool) := f (move hn
      (if b then d*(((z.2.1 0).val:ℤ)-((z.2.2 0).val:ℤ)) else 0) z.1)
    have h (ω : Vertex 1) :
        f (move hn (ActualTZFiniteBoxes318.shift (fun _=>d) z.2.1 z.2.2 ω) z.1)=Y (v ω) := by
      have hv : v ω=ω 0 := rfl
      rw [hv]
      simp only [ActualTZFiniteBoxes318.shift,Fin.sum_univ_one,Y]
    change (∏ ω : Vertex 1,
      f (move hn (ActualTZFiniteBoxes318.shift (fun _=>d) z.2.1 z.2.2 ω) z.1))=
      f z.1*f (move hn (d*(((z.2.1 0).val:ℤ)-((z.2.2 0).val:ℤ))) z.1)
    calc
      _ = ∏ ω : Vertex 1,Y (v ω) := Finset.prod_congr rfl (fun ω _=>h ω)
      _ = ∏ b : Bool,Y b := v.prod_comp Y
      _ = _ := by
        simp only [Fintype.prod_bool,Y,if_true,Bool.false_eq_true,if_false,move_zero,mul_comm]
  have hC : (Fintype.card (Fin n×Pair M):ℝ)=(n:ℝ)*((2*M+1:ℕ):ℝ)^(2*1:ℕ) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.mul_one,pow_two]
  unfold boxPower prob
  rw [hC]
  congr 1
  calc
    _ = ∑ z : CubeArgs n 1 (2*M+1),F (E z) := Finset.sum_congr rfl (fun z _=>hProd z)
    _ = _ := E.sum_comp F

@[expose] def localMean (A : Fin s→ℤ) (hn : 0<n) (f : Fin n→ℝ) : ℝ :=
  prob (fun h : Fine s M=>boxNorm n 1 (2*M+1) hn (fun _=>slope A h) f)

/-- The actual mean local power is a single shared-x pairing
with the local dual. Ordered endpoints are not collapsed. -/
theorem mean_power (A : Fin s→ℤ) (hn : 0<n) (e : Fin n→ℝ) :
    prob (fun x=>e x*action (M:=M) A hn e x)=
      prob (fun h : Fine s M=>boxPower n 1 (2*M+1) hn (fun _=>slope A h) e) := by
  simp only [action,←prob_left]
  let E (x : Fin n) (h : Fine s M) (z : Pair M) := e x*e (move hn
    (slope A h*((z.1.val:ℤ)-(z.2.val:ℤ))) x)
  calc
    _ = prob (fun x=>prob (fun h : Fine s M=>prob (fun t : Pair M=>E x h t))) := by
      simp only [nested,E,step]
    _ = prob (fun h : Fine s M=>prob (fun x=>prob (fun t : Pair M=>E x h t))) :=
      prob_swap (fun x h=>prob (fun t : Pair M=>E x h t))
    _ = _ := by
      congr 1
      funext h
      rw [nested,one_slice] <;> rfl

end ActualTZOneAxisLocalDual318
