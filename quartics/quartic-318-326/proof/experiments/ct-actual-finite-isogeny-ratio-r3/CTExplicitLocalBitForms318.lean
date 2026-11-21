module
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
public section

namespace CTExplicitLocalBitForms318

abbrev B := ZMod 2

/-- Odd coordinates: valuation parity, residue-character bit. -/
def odd (k : B) (a b : B × B) : B :=
  k*a.1*b.1+a.1*b.2+a.2*b.1

/-- Dyadic coordinates: valuation parity, epsilon unit bit, omega unit bit. -/
def dyadic (a b : B × B × B) : B :=
  a.2.1*b.2.1+a.1*b.2.2+a.2.2*b.1

theorem odd_symm (k : B) (a b : B × B) : odd k a b=odd k b a := by
  unfold odd
  ring

theorem dyadic_symm (a b : B × B × B) : dyadic a b=dyadic b a := by
  unfold dyadic
  ring

theorem odd_nondegenerate (k : B) (a : B × B)
    (h : ∀ b, odd k a b=0) : a=(0,0) := by
  have h₁ : a.1=0 := by simpa [odd] using h (0,1)
  have h₂ : a.2=0 := by simpa [odd,h₁] using h (1,0)
  exact Prod.ext h₁ h₂

theorem dyadic_nondegenerate (a : B × B × B)
    (h : ∀ b, dyadic a b=0) : a=(0,0,0) := by
  have h₁ : a.1=0 := by simpa [dyadic] using h (0,0,1)
  have h₂ : a.2.1=0 := by simpa [dyadic] using h (0,1,0)
  have h₃ : a.2.2=0 := by simpa [dyadic] using h (1,0,0)
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

/-- The dyadic forward nontrivial unit 5 = class(-3) has bits (0,0,1).
Its orthogonal plane is exactly valuation parity zero. -/
theorem dyadic_orthogonal_five (a : B × B × B) : dyadic a (0,0,1)=0 ↔ a.1=0 := by
  simp [dyadic]

/-- At a split ramified odd place, source class n and target class
4nw have the same odd valuation; their unit bits differ by k. -/
theorem ramified_split_orthogonal (k u : B) : odd k (1,u) (1,u+k)=0 := by
  have h2 : (2:B)=0 := by decide
  calc
    odd k (1,u) (1,u+k)=2*(k+u) := by unfold odd; ring
    _=0 := by rw [h2,zero_mul]

/-- The literal root orientation identifying the target unit bit:
if w²−w+1=0, then −w=(w²)², without any square-root choice. -/
theorem ramified_root_neg_square {K : Type*} [CommRing K] (w : K)
    (h : w^2-w+1=0) : -w=(w^2)^2 := by
  linear_combination -(w^2+w)*h

end CTExplicitLocalBitForms318

#print axioms CTExplicitLocalBitForms318.dyadic_nondegenerate
#print axioms CTExplicitLocalBitForms318.ramified_split_orthogonal
