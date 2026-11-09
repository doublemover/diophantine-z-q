module
public import OriginalTraceBoundary318
public section
noncomputable section
namespace PushedUnitCocycleRealization318
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
/-- A cocycle of actual pushed units is realized on the literal full preimage
cover. Only original inverse-image maps and intersection identities are used. -/
@[expose] def realize
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.pushedUnits g).obj U) :
    UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj (fun i => g ⁻¹ᵁ U i) where
  transition i j := c.transition i j
  diagonal i := c.diagonal i
  triple i j k := c.triple i j k
lemma transition
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.pushedUnits g).obj U) (i j : ι) :
    (realize g U c).transition i j = c.transition i j := rfl
lemma gauge {c d : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.pushedUnits g).obj U}
    (h : UnitTransitionCocycle318.GaugeEquivalent c d) :
    UnitTransitionCocycle318.GaugeEquivalent (realize g U c) (realize g U d) := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,ha⟩
end PushedUnitCocycleRealization318
