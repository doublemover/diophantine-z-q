module
public import InverseImageLineCocycle318
public import LineSheafInverse318
public section
noncomputable section
namespace InverseImageInverseCocycle318
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) {ι : Type u} (U : ι → Y.Opens)
  (e : ∀ i,SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅ M.restrict (f ⁻¹ᵁ U i).ι)

/-- Original inverse-frame transitions, read on the SAME complete
inverse-image overlaps. No identification from stalks or generic points. -/
lemma inverse :
    InverseImageLineCocycle318.cocycle f
      (LineSheafInverse318.object M (fun i => f ⁻¹ᵁ U i) e) U
      (LineSheafInverse318.frame M (fun i => f ⁻¹ᵁ U i) e)=
    UnitCocycleInverse318.inverse (InverseImageLineCocycle318.cocycle f M U e) := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  have h := congrArg (fun q => q.transition i j)
    (LineSheafInverse318.original_inverse_transitions M (fun i => f ⁻¹ᵁ U i) e)
  exact h
end InverseImageInverseCocycle318
