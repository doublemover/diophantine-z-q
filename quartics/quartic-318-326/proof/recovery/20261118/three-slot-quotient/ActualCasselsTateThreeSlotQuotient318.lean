module
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public section

/-! A three-cocycle trivial on each kernel slot factors in its actual
arguments AND has kernel-fixed values. No action of Q on all of A is used. -/
namespace ActualCasselsTateThreeSlotQuotient318
variable {G Q A : Type*} [Group G] [Group Q] [CommGroup A]
  [MulDistribMulAction G A] (π : G →* Q) (w : G → G → G → A)
  (hc : ∀ x y z t, (x • w y z t) * w x (y*z) t * w x y z =
    w (x*y) z t * w x y (z*t))
  (h₁ : ∀ a y z, π a = 1 → w a y z = 1)
  (h₂ : ∀ x a z, π a = 1 → w x a z = 1)
  (h₃ : ∀ x y a, π a = 1 → w x y a = 1)

include hc h₃ in
lemma last_eq (x y z z' : G) (hz : π z = π z') : w x y z = w x y z' := by
  have ha : π (z⁻¹*z') = 1 := by rw [map_mul, map_inv, hz, inv_mul_cancel]
  have e := hc x y z (z⁻¹*z')
  simpa only [h₃ y z _ ha, h₃ x (y*z) _ ha, h₃ (x*y) z _ ha, smul_one, one_mul, mul_inv_cancel_left] using e

include hc h₂ h₃ in
lemma middle_eq (x y y' z : G) (hy : π y = π y') : w x y z = w x y' z := by
  let a := y⁻¹*y'
  have ha : π a = 1 := by simp only [a, map_mul, map_inv, hy, inv_mul_cancel]
  have e := hc x y a z
  have E : w x y' z = w x y (a*z) := by
    simpa only [h₂ y a z ha, h₃ x y a ha, h₂ (x*y) a z ha, smul_one, one_mul, mul_one,
      a, mul_inv_cancel_left] using e
  exact (last_eq π w hc h₃ x y z (a*z) (by rw [map_mul, ha, one_mul])).trans E.symm

include hc h₁ h₂ h₃ in
lemma first_eq (x x' y z : G) (hx : π x = π x') : w x y z = w x' y z := by
  let a := x⁻¹*x'
  have ha : π a = 1 := by simp only [a, map_mul, map_inv, hx, inv_mul_cancel]
  have e := hc x a y z
  have E : w x (a*y) z = w x' y z := by
    simpa only [h₁ a y z ha, h₂ x a y ha, h₂ x a (y*z) ha, smul_one, one_mul, mul_one,
      a, mul_inv_cancel_left] using e
  exact (middle_eq π w hc h₂ h₃ x y (a*y) z (by rw [map_mul, ha, one_mul])).trans E

include hc h₁ h₂ h₃ in
lemma kernel_fixes (a x y z : G) (ha : π a = 1) : a • w x y z = w x y z := by
  have e := hc a x y z
  have E : a • w x y z = w (a*x) y z := by simpa only [h₁ a (x*y) z ha, h₁ a x y ha, h₁ a x (y*z) ha, mul_one] using e
  exact E.trans (first_eq π w hc h₁ h₂ h₃ (a*x) x y z (by rw [map_mul, ha, one_mul]))

include hc h₁ h₂ h₃ in
/-- The descended cochain is closed with the quotient action on the fixed
coefficients expressed by ANY lift. In particular no homomorphic section
or action of Q on the nonfixed coefficients is presupposed. -/
theorem exists_quotient_three (s : Q → G) (hs : ∀ q, π (s q) = q) :
    ∃ v : Q → Q → Q → A,
      (∀ x y z, w x y z = v (π x) (π y) (π z)) ∧
      (∀ a q r t, π a = 1 → a • v q r t = v q r t) ∧
      (∀ (g : G) (q r t : Q), (g • v q r t) * v (π g) (q*r) t * v (π g) q r =
        v (π g*q) r t * v (π g) q (r*t)) := by
  let v : Q → Q → Q → A := fun q r t => w (s q) (s r) (s t)
  have hf : ∀ x y z, w x y z = v (π x) (π y) (π z) := by
    intro x y z
    change w x y z = w (s (π x)) (s (π y)) (s (π z))
    calc
      _ = w (s (π x)) y z := first_eq π w hc h₁ h₂ h₃ _ _ _ _ (hs _).symm
      _ = w (s (π x)) (s (π y)) z := middle_eq π w hc h₂ h₃ _ _ _ _ (hs _).symm
      _ = _ := last_eq π w hc h₃ _ _ _ _ (hs _).symm
  refine ⟨v, hf, ?_, ?_⟩
  · intro a q r t ha
    exact kernel_fixes π w hc h₁ h₂ h₃ a (s q) (s r) (s t) ha
  · intro g q r t
    simpa only [hf, map_mul, hs] using hc g (s q) (s r) (s t)
end ActualCasselsTateThreeSlotQuotient318
