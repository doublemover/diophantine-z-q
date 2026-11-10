module
public import LinePullbackTransitions318
public import OriginalFunctionTransport318
public section
noncomputable section
namespace OriginalPullbackFrameCocycle318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Canonical original pulled frame on the specified whole inverse-image
open. The only transport is the supplied equality of original opens. -/
@[expose] def frameOn (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V)
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) :
    SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback f).obj M).restrict V.ι :=
  h ▸ LinePullbackFrames318.frame f M U e

variable {ι : Type u} (U : ι → Y.Opens) (V : ι → X.Opens)
  (h : ∀ i, f ⁻¹ᵁ U i = V i)
  (em : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)

/-- Actual extracted source cocycle on the entire source intersections.
This discharges canonical frame coherence and explicitly normalizes the
inverse image of an intersection; no frame-compatibility premise remains. -/
lemma transition (i j : ι) :
    (LineFrameCocycle318.cocycle ((Scheme.Modules.pullback f).obj M) V
      (fun k => frameOn f M (U k) (V k) (h k) (em k))).transition i j =
    Units.map (OriginalFunctionTransport318.pullTo f (U i ⊓ U j) (V i ⊓ V j)
      (by rw [Scheme.Hom.preimage_inf,h i,h j])).toMonoidHom
      ((LineFrameCocycle318.cocycle M U em).transition i j) := by
  have hV : (fun k => f ⁻¹ᵁ U k) = V := funext h
  subst V
  have hc := congrArg (fun q => q.transition i j)
    (LinePullbackTransitions318.cocycle f M U em)
  have hr := congrArg
    (Units.map (X.presheaf.map (homOfLE (Scheme.Hom.preimage_inf f (U i) (U j)).ge).op).hom.toMonoidHom) hc
  change Units.map _
    (LineFrameTransitions318.scalar ((Scheme.Modules.pullback f).obj M)
      (fun k => f ⁻¹ᵁ U k) (fun k => LinePullbackFrames318.frame f M (U k) (em k))
      i j (f ⁻¹ᵁ (U i ⊓ U j)) _ _) = _ at hr
  rw [LineFrameTransitions318.restrict] at hr
  exact hr
end OriginalPullbackFrameCocycle318
