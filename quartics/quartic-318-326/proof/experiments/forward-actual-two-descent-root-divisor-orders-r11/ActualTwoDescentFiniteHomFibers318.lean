module
public import ActualTwoDescentFourActualShaConsumer318
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion
public section
noncomputable section
namespace ActualTwoDescentFiniteHomFibers318
set_option maxHeartbeats 16000000

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A literal injection into target times kernel, using one chosen representative per nonempty fiber. -/
lemma actual_hom_fiber_embedding (f : G →* H) : ∃ e : G → H × f.ker, Function.Injective e := by
  classical
  let s (h : H) : G := if hh : ∃ g, f g=h then Classical.choose hh else 1
  have hs (g : G) : f (s (f g))=f g := by
    dsimp [s]
    rw [dif_pos ⟨g,rfl⟩]
    exact Classical.choose_spec (show ∃ x, f x=f g from ⟨g,rfl⟩)
  let e (g : G) : H × f.ker := (f g,⟨g/(s (f g)),by
    change f (g/s (f g))=1
    rw [map_div,hs,div_self]⟩)
  refine ⟨e,?_⟩
  intro x y h
  have h1 : f x=f y := congrArg Prod.fst h
  have h2 : x/s (f x)=y/s (f y) := congrArg (fun z : H × f.ker => (z.2 : G)) h
  rw [h1] at h2
  exact (div_left_inj).mp h2

lemma actual_finite_of_finite_kernel_target (f : G →* H) [Finite H] [Finite f.ker] : Finite G := by
  obtain ⟨e,he⟩ := actual_hom_fiber_embedding f
  exact Finite.of_injective e he

lemma actual_card_le_kernel_target (f : G →* H) [Finite H] [Finite f.ker] :
    Nat.card G ≤ Nat.card H*Nat.card f.ker := by
  obtain ⟨e,he⟩ := actual_hom_fiber_embedding f
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective e he

end ActualTwoDescentFiniteHomFibers318
