module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Hom.Basic
public section
namespace ActualCasselsTateFiniteThreeProduct318
open scoped BigOperators
variable {G A : Type*} [Group G] [Fintype G] [CommGroup A]
variable (act : G → A →* A)

/-- Genuine first-slot action; the producer only needs the indicated
endomorphisms because the actual 3-cocycle equation is a hypothesis. -/
def dTwo (b : G → G → A) (g h l : G) : A :=
  act g (b h l) / b (g*h) l * b g (h*l) / b g h

def productLast (c : G → G → G → A) (g h : G) : A := ∏ t : G, c g h t

private def leftShift (l : G) : G ≃ G where
  toFun t := l*t
  invFun t := l⁻¹*t
  left_inv _ := inv_mul_cancel_left _ _
  right_inv _ := mul_inv_cancel_left _ _

/-- Pointwise primitive for the group-order power of THIS finite-stage
3-cocycle. Works on nonnormalized cochains and nontrivial actions. -/
theorem inverse_product_primitive (c : G → G → G → A)
    (hc : ∀ g h l t, act g (c h l t) / c (g*h) l t * c g (h*l) t /
      c g h (l*t) * c g h l = 1) (g h l : G) :
    dTwo act (fun x y => (productLast c x y)⁻¹) g h l = (c g h l)^(Fintype.card G) := by
  classical
  have H := congrArg (fun f : G → A => ∏ t, f t) (funext (hc g h l))
  have hs : (∏ t : G, c g h (l*t)) = ∏ t : G, c g h t := (leftShift l).prod_comp _
  have H' : dTwo act (productLast c) g h l * (c g h l)^(Fintype.card G) = 1 := by
    simpa only [dTwo,productLast,Finset.prod_mul_distrib,Finset.prod_div_distrib,
      Finset.prod_const,Finset.card_univ,←map_prod,hs,one_pow] using H
  have he : (c g h l)^(Fintype.card G) = (dTwo act (productLast c) g h l)⁻¹ := by
    calc
      _ = (dTwo act (productLast c) g h l)⁻¹ *
        (dTwo act (productLast c) g h l * (c g h l)^(Fintype.card G)) :=
          (inv_mul_cancel_left _ _).symm
      _ = _ := by rw [H',mul_one]
  rw [he]
  simp only [dTwo,map_inv,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ac_rfl
end ActualCasselsTateFiniteThreeProduct318
