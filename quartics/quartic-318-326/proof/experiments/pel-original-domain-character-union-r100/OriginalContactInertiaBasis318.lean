module
public import InertiaLabels318
public import FourBinaryCharacters318
public section
noncomputable section
namespace OriginalContactInertiaBasis318
open Matrix InertiaLabels318
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Contact-coordinate order is105,70,42,30, whereas the published arithmetic
rows are30,42,70,105. This explicit permutation is part of the map. -/
@[expose] def reverse (k : Fin 4) : Fin 4 := ![3,2,1,0] k
lemma reverse_reverse : ∀ k, reverse (reverse k) = k := by decide

/-- The SAME arithmetic prime-exponent vector becomes coordinates in the
original four finite inertia generators, in the actual contact order. -/
@[expose] def basis : Multiplicative V ≃* FourBinaryCharacters318.Group where
  toFun v k := Multiplicative.ofAdd ((labels *ᵥ Multiplicative.toAdd v) (reverse k))
  invFun w := Multiplicative.ofAdd (labels *ᵥ (fun i => Multiplicative.toAdd (w (reverse i))))
  left_inv v := by
    change labels *ᵥ (fun i => (labels *ᵥ Multiplicative.toAdd v) (reverse (reverse i))) =
      Multiplicative.toAdd v
    simp only [reverse_reverse]
    exact coefficient_map_involutive _
  right_inv w := by
    funext k
    change Multiplicative.ofAdd
      ((labels *ᵥ (labels *ᵥ (fun i => Multiplicative.toAdd (w (reverse i))))) (reverse k)) = w k
    rw [coefficient_map_involutive,reverse_reverse]
    all_goals rfl
  map_mul' v w := by
    funext k
    change Multiplicative.ofAdd
      ((labels *ᵥ (Multiplicative.toAdd v + Multiplicative.toAdd w)) (reverse k)) = _
    rw [Matrix.mulVec_add]
    all_goals rfl

/-- All four original finite inertia labels, not only an abstract basis. -/
lemma basis_finite : ∀ k : Fin 4,
    basis (Multiplicative.ofAdd (labels (reverse k))) = FourBinaryCharacters318.flip k := by
  decide

lemma finite_divisors : ∀ k : Fin 4,
    divisor (labels (reverse k)) = (![105,70,42,30] : Fin 4 → ℕ) k := by decide

/-- The original arithmetic210 label is exactly the product of all four
finite contact flips, retaining the fifth/infinity inertia relation. -/
lemma basis_fifth : basis (Multiplicative.ofAdd (fun _ => (1 : ZMod 2))) =
    ∏ k : Fin 4, FourBinaryCharacters318.flip k := by decide

lemma finite_iff (w : Multiplicative V) (k : Fin 4) :
    basis w = FourBinaryCharacters318.flip k ↔ w = Multiplicative.ofAdd (labels (reverse k)) := by
  rw [← basis_finite k]
  exact basis.injective.eq_iff
end OriginalContactInertiaBasis318
