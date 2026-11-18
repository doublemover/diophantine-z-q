module
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Tactic.Abel
public section

/-! Real C₂ acts by inversion, written additively. Its non-normalized
degree-three cocycles become explicit boundaries once each old coefficient
has SOME half in the new group. No homomorphism of chosen halves is required. -/
namespace ActualCasselsTateRealThreeSquareLift318
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
private def op (x y : Bool) : Bool := if x then !y else y
private def act {C : Type*} [AddCommGroup C] (g : Bool) (m : C) : C :=
  if g then -m else m

def realClosed (c : Bool → Bool → Bool → A) : Prop :=
  ∀ g h k l, act g (c h k l) - c (op g h) k l + c g (op h k) l -
    c g h (op k l) + c g h k = 0

def realBoundary {C : Type*} [AddCommGroup C] (b : Bool → Bool → C) (g h k : Bool) : C :=
  act g (b h k) - b (op g h) k + b g (op h k) - b g h

theorem boundary_after_half_lift (f : A →+ B) (half : ∀ u : A, ∃ v : B, v + v = f u)
    (c : Bool → Bool → Bool → A) (hc : realClosed c) :
    ∃ b : Bool → Bool → B, ∀ g h k, realBoundary b g h k = f (c g h k) := by
  have h000 : c false false false = 0 := by
    simpa [act, op] using hc false false false false
  have h010 : c false true false = 0 := by
    simpa [act, op] using hc false true false false
  have h011 : c false true true + c false false true = 0 := by
    simpa [act, op, h000] using hc false false true true
  have h101 : -c false false true - c true false true + c true false false = 0 := by
    simpa [act, op] using hc true false false true
  have h110 : -c true false false + c true true false = 0 := by
    simpa [act, op,h000] using hc true true false false
  have e011 : c false true true = -c false false true := by
    calc
      _ = (c false true true + c false false true) - c false false true := by abel
      _ = _ := by rw [h011]; abel
  have e101 : c true false true = c true false false - c false false true := by
    calc
      _ = (c true false false - c false false true) -
        (-c false false true - c true false true + c true false false) := by abel
      _ = _ := by rw [h101]; abel
  have e110 : c true true false = c true false false := by
    calc
      _ = c true false false + (-c true false false + c true true false) := by abel
      _ = _ := by rw [h110]; abel
  obtain ⟨v,hv⟩ := half (c true false false + c false false true + c true true true)
  simp only [map_add] at hv
  let b : Bool → Bool → B := fun x y =>
    if x then (if y then -v else -f (c true false false))
    else (if y then f (c false false true) else 0)
  refine ⟨b,?_⟩
  intro g h k
  cases g <;> cases h <;> cases k <;> simp only [realBoundary,b,act,op,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
    h000,h010,e011,e101,e110,map_zero,map_neg,map_sub]
    <;> first | abel1 | (
      calc
        _ = (v + v) - f (c true false false) - f (c false false true) := by abel
        _ = _ := by rw [hv]; abel)
end ActualCasselsTateRealThreeSquareLift318
