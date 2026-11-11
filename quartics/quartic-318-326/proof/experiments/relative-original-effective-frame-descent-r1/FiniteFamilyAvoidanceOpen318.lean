module
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section
namespace FiniteFamilyAvoidanceOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z B X : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p] (q : Z ⟶ X) (U : X.Opens)
/-- The actual open locus where the WHOLE family lies in the chosen
source open: remove the closed image of its closed complement. -/
@[expose] def locus : B.Opens :=
  ⟨(p '' (q ⁻¹' (U : Set X)ᶜ))ᶜ,
    (p.isClosedMap _ (U.isOpen.isClosed_compl.preimage q.continuous)).isOpen_compl⟩
lemma mem_locus (b : B) : b∈locus p q U ↔ ∀ z : Z, p z=b → q z∈U := by
  classical
  constructor
  · intro hb z hz
    by_contra h
    exact hb ⟨z,h,hz⟩
  · intro hb hbad
    obtain ⟨z,hz,hpb⟩ := hbad
    exact hz (hb z hpb)
/-- Membership tests the entire scheme fiber's underlying support, not
selected rational points, reduced coordinates or chart basis vectors. -/
lemma whole_fiber (b : B) : b∈locus p q U ↔ p ⁻¹' {b} ⊆ q ⁻¹' (U : Set X) := by
  rw [mem_locus]
  rfl
end FiniteFamilyAvoidanceOpen318
