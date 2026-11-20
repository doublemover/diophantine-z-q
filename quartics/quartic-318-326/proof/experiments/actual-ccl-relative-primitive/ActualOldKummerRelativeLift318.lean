module
public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Abel
public section

namespace ActualOldKummerRelativeLift318

variable {U₀ U₁ V₀ V₁ : Type*}
variable [AddCommGroup U₀] [AddCommGroup U₁] [AddCommGroup V₀] [AddCommGroup V₁]

/-- Same old local slot of d(p,u,q) = (dp,du,loc p−i u−dq).
Here w is the already chosen norm primitive, q the difference of the
original H22 local entries, and l the localization of the *given*
global primitive. Nonnegative models make H⁰ the actual closed
degree-zero subgroups; injectivity in H¹ supplies the first lift. -/
theorem lift_same_global_entry
    (dU : U₀ →+ U₁) (dV : V₀ →+ V₁)
    (i₀ : U₀ →+ V₀) (i₁ : U₁ →+ V₁)
    (comm : ∀ x, dV (i₀ x) = i₁ (dU x))
    (inj₁ : ∀ u : U₁, (∃ v : V₀, dV v = i₁ u) → ∃ x, dU x = u)
    (surj₀ : ∀ v : V₀, dV v = 0 → ∃ x, dU x = 0 ∧ i₀ x = v)
    (inj₀ : ∀ x : U₀, dU x = 0 → i₀ x = 0 → x = 0)
    (l w q : V₀) (u : U₁)
    (hw : dV l = dV w) (hq : dV q = dV w - i₁ u) :
    ∃! x : U₀, dU x = u ∧ i₀ x = l - q := by
  have hu : dV (w - q) = i₁ u := by rw [map_sub,hq]; abel
  obtain ⟨x₀,hx₀⟩ := inj₁ u ⟨w-q,hu⟩
  have hA : dV (w-q-i₀ x₀) = 0 := by
    rw [map_sub,hu,comm,hx₀,sub_self]
  have hB : dV (l-w) = 0 := by rw [map_sub,hw,sub_self]
  obtain ⟨xA,hA₁,hA₂⟩ := surj₀ _ hA
  obtain ⟨xB,hB₁,hB₂⟩ := surj₀ _ hB
  have hmain : dU (x₀+xA+xB) = u ∧ i₀ (x₀+xA+xB) = l-q := by
    constructor
    · simp only [map_add,hx₀,hA₁,hB₁,add_zero]
    · rw [map_add,map_add,hA₂,hB₂]; abel
  refine ⟨x₀+xA+xB,hmain,?_⟩
  intro y hy
  have hzero : y-(x₀+xA+xB) = 0 := inj₀ _
    (by rw [map_sub,hy.1,hmain.1,sub_self])
    (by rw [map_sub,hy.2,hmain.2,sub_self])
  exact sub_eq_zero.mp hzero

/-- On the actual old rational bar slot the invariant Tate module vanishes.
This applies to a primitive in THAT module, not to a finite torsion point
by a nonexistent coefficient map from Z/(2^a) to Q₂. -/
theorem rational_primitive_eq
    (dV : V₀ →+ V₁) (inj : ∀ v, dV v = 0 → v = 0)
    (l w : V₀) (h : dV l = dV w) : l = w :=
  sub_eq_zero.mp (inj (l-w) (by rw [map_sub,h,sub_self]))

variable {X₂ X₃ Y₀ Y₁ R : Type*}
variable [AddCommGroup X₂] [AddCommGroup X₃]
variable [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup R]

/-- The degree-two row of the same compact pairing into R[-3].
Chain adjunction, not agreement on exact cycles, yields this sign.
In the actual comparison y and y' are the two orthogonal lifts of
the original and norm classes; v is the image of their degree-zero
boundary under the very same conjugation and j-inverse. -/
theorem paired_row_diff_at
    (dX : X₂ →+ X₃) (dY : Y₀ →+ Y₁)
    (P₂₁ : X₂ →+ Y₁ →+ R) (P₃₀ : X₃ →+ Y₀ →+ R)
    (adj : ∀ x v, P₃₀ (dX x) v + P₂₁ x (dY v) = 0)
    (y y' : Y₁) (v : Y₀) (h : y-y' = dY v) (x : X₂) :
    P₂₁ x y - P₂₁ x y' = - P₃₀ (dX x) v := by
  rw [←map_sub,h]
  have ha := adj x v
  calc
    P₂₁ x (dY v) = P₂₁ x (dY v) + P₃₀ (dX x) v - P₃₀ (dX x) v := by abel
    _ = - P₃₀ (dX x) v := by rw [add_comm (P₂₁ x (dY v)),ha,zero_sub]

end ActualOldKummerRelativeLift318

#print axioms ActualOldKummerRelativeLift318.lift_same_global_entry
#print axioms ActualOldKummerRelativeLift318.rational_primitive_eq
#print axioms ActualOldKummerRelativeLift318.paired_row_diff_at
