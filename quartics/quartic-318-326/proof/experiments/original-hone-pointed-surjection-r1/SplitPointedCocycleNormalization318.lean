module
public import SplitOpenUnitLift318
public section
noncomputable section
namespace SplitPointedCocycleNormalization318
open AlgebraicGeometry CategoryTheory Opposite
open PointedLineDeformation318 UnitTransitionCocycle318
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (r : X ⟶ X₀) (hr : i ≫ r = 𝟙 X₀)
    (L : Deformation i) {κ : Type u} (U : κ → X.Opens)
    (frames : ∀ k, SheafOfModules.unit (U k).toScheme.ringCatSheaf ≅ L.line.object.restrict (U k).ι)
    (stable : ∀ k, U k ≤ r ⁻¹ᵁ (i ⁻¹ᵁ U k))
@[expose] def liftedGauge (k : κ) : Γ(X,U k)ˣ :=
  SplitOpenUnitLift318.unitLift i r (U k) (stable k)
    (PointedCocycleReductionGauge318.gauge i L U frames k)
@[expose] def normalized : Cocycle (StructureUnitsSheaf318.units X).obj U :=
  UnitCocycleTwist318.twist _ U (LineFrameCocycle318.cocycle L.line.object U frames)
    (liftedGauge i r L U frames stable)
include hr in
/-- The ACTUAL reduced cocycle is identically one on every whole overlap.
The supplied special-fiber trivialization determines the gauge being lifted. -/
lemma reduction :
    UnitTransitionCocycle318.map (Functor.whiskerRight i.c OpenUnitNorm318.unitsFunctor)
      (normalized i r L U frames stable) =
        UnitCocycleOne318.one (StructureUnitsSheaf318.pushedUnits i).obj U := by
  rw [normalized, UnitCocycleTwist318.map_twist]
  have ha : (fun k => (Functor.whiskerRight i.c OpenUnitNorm318.unitsFunctor).app (op (U k))
      (liftedGauge i r L U frames stable k)) = PointedCocycleReductionGauge318.gauge i L U frames := by
    funext k
    exact SplitOpenUnitLift318.reduction_unit i r hr (U k) (stable k) _
  rw [ha]
  apply Cocycle.ext
  intro k l
  exact (PointedCocycleReductionGauge318.equation i L U frames k l).symm
include hr in
lemma transition_reduces (k l : κ) :
    Units.map (i.app (U k ⊓ U l)).hom.toMonoidHom
      ((normalized i r L U frames stable).transition k l) = 1 := by
  exact congrArg (fun c => c.transition k l) (reduction i r hr L U frames stable)
variable (hc : (⊤ : X.Opens) ≤ ⨆ k, U k)
/-- Reconstruction is an isomorphism of the original module sheaf, followed
by the actual lifted unit gauge. No quotient or cohomology label is substituted. -/
@[expose] def reconstruction : L.line.object ≅
    CocycleModule318.object U (normalized i r L U frames stable) :=
  LineFrameReconstructionIso318.iso L.line.object U frames hc ≪≫
    CocycleGaugeIso318.iso U (LineFrameCocycle318.cocycle L.line.object U frames)
      (normalized i r L U frames stable) (liftedGauge i r L U frames stable) (fun _ _ => rfl)
end SplitPointedCocycleNormalization318
