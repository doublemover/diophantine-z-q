module
public import OpenSheafTransition318
public section
noncomputable section
namespace OpenSheafGluing318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : Data U M)
abbrev sheaf := OpenModuleGluedSheaf318.sheaf D.sectionData
abbrev overIso (i : ι) := OpenModuleGluedSheaf318.overIso D.sectionData i
abbrev chartIso (i : ι) := OpenModuleGluedSheaf318.chartIso D.sectionData i

/-- Recovered chart isomorphisms realize exactly the original sheaf
transition on each genuine pairwise overlap, not only on section classes. -/
lemma transition_recovered (i j : ι) :
    restrictIso (overIso D i) (show U i ⊓ U j ≤ U i from inf_le_left) ≪≫ D.transition i j =
      restrictIso (overIso D j) (show U i ⊓ U j ≤ U j from inf_le_right) := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  change component (D.transition i j) V.unop.left (leOfHom V.unop.hom)
      (component (restrictIso (overIso D i) inf_le_left) V.unop.left (leOfHom V.unop.hom) s) =
    component (restrictIso (overIso D j) inf_le_right) V.unop.left (leOfHom V.unop.hom) s
  rw [component_restrict, component_restrict]
  exact OpenModuleChartRecovery318.evaluate_transition D.sectionData i j V.unop.left
    ((leOfHom V.unop.hom).trans inf_le_left) ((leOfHom V.unop.hom).trans inf_le_right) s

/-- Non-affine module-sheaf gluing with actual chart comparisons satisfying
the original overlap squares. This is object effectivity for this open cover. -/
theorem effective : ∃ (G : X.Modules) (e : ∀ i, G.over (U i) ≅ (M i).over (U i)),
    ∀ i j,
      restrictIso (e i) (show U i ⊓ U j ≤ U i from inf_le_left) ≪≫ D.transition i j =
        restrictIso (e j) (show U i ⊓ U j ≤ U j from inf_le_right) :=
  ⟨sheaf D, overIso D, transition_recovered D⟩
end OpenSheafGluing318
