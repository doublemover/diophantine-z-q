module
public import PointedFrameMap318
public section
noncomputable section
namespace UnitCocyclePointedGauge318
open AlgebraicGeometry CategoryTheory PointedLineDeformation318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Equality of maps into the original framed sheaf follows from all original
coordinate maps, because reconstruction retains that same sheaf. -/
lemma coordinate_hom_ext {X : Scheme.{u}} {M N : X.Modules} {ι : Type u}
    (U : ι → X.Opens)
    (en : ∀ a, SheafOfModules.unit (U a).toScheme.ringCatSheaf ≅ N.restrict (U a).ι)
    (hc : (⊤ : X.Opens) ≤ ⨆ a, U a) (g h : M ⟶ N)
    (he : ∀ a, g ≫ LineFrameAdjunction318.coordinate N (U a) (en a) =
      h ≫ LineFrameAdjunction318.coordinate N (U a) (en a)) : g = h := by
  apply (cancel_mono (LineFrameReconstructionIso318.iso N U en hc).hom).mp
  apply CocycleModule318.hom_ext U (LineFrameCocycle318.cocycle N U en)
  intro a
  simpa only [Category.assoc, LineFrameReconstructionIso318.hom_coefficient] using he a
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (c d : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (hc : (⊤ : X.Opens) ≤ ⨆ a, U a)
    (rc : UnitCocyclePointedLine318.ReducesToOne i U c)
    (rd : UnitCocyclePointedLine318.ReducesToOne i U d)
    (a : ∀ k, Γ(X,U k)ˣ)
    (hg : ∀ k l, d.transition k l = UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.units X).obj U a k l * c.transition k l)
    (ha : ∀ k, i.app (U k) (a k).val = 1)
/-- The actual old gauge isomorphism, not a replacement chosen to preserve
frames, respects the constructed special-fiber trivialization. -/
include ha in
lemma compatible :
    (Scheme.Modules.pullback i).map (CocycleGaugeIso318.iso U c d a hg).hom ≫
      (UnitCocyclePointedLine318.trivialization i U d hc rd).hom =
        (UnitCocyclePointedLine318.trivialization i U c hc rc).hom := by
  apply coordinate_hom_ext (fun k => i ⁻¹ᵁ U k)
    (fun k => StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U k))
    (LinePullbackFrames318.preimage_cover i U hc)
  intro k
  rw [Category.assoc, UnitCocyclePointedLine318.trivialization_coordinate,
    UnitCocyclePointedLine318.trivialization_coordinate]
  apply PointedFrameMap318.pulled_coordinate i (CocycleGaugeIso318.iso U c d a hg).hom (U k)
    (CocycleCanonicalTransitions318.frames U c k) (CocycleCanonicalTransitions318.frames U d k)
    ((U k).topIso.inv (a k).val)
  · rw [CocycleCanonicalTransitions318.coordinate, CocycleCanonicalTransitions318.coordinate]
    exact CocycleGaugeIso318.hom_coefficient U c d a hg k
  · exact PointedFrameMap318.chart_scalar_one i (U k) (a k).val (ha k)
@[expose] def pointedIso :
    PointedIso i (UnitCocyclePointedLine318.deformation i U c hc rc)
      (UnitCocyclePointedLine318.deformation i U d hc rd) where
  iso := CocycleGaugeIso318.iso U c d a hg
  compatible := compatible i U c d hc rc rd a hg ha
include a hg ha in
lemma class_eq :
    classOf i (UnitCocyclePointedLine318.deformation i U c hc rc) =
      classOf i (UnitCocyclePointedLine318.deformation i U d hc rd) :=
  (classOf_eq_iff i _ _).2 ⟨pointedIso i U c d hc rc rd a hg ha⟩
end UnitCocyclePointedGauge318
