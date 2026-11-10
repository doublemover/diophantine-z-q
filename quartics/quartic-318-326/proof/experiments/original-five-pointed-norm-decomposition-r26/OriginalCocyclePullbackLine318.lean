module
public import UnitCocycleSchemeRefinement318
public import CocycleRefinementIso318
public section
noncomputable section
namespace OriginalCocyclePullbackLine318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units Y).obj U)
abbrev M := CocycleModule318.object U c
abbrev pulled := (Scheme.Modules.pullback f).obj (M U c)
@[expose] def fullFrames (a : ι) :
    SheafOfModules.unit (f ⁻¹ᵁ U a).toScheme.ringCatSheaf ≅ (pulled f U c).restrict (f ⁻¹ᵁ U a).ι :=
  LinePullbackFrames318.frame f (M U c) (U a) (CocycleCanonicalTransitions318.frames U c a)
/-- Canonical frames of the ORIGINAL pulled sheaf have exactly the original
coefficient-map unit transitions on complete inverse images. -/
lemma full_cocycle :
    LineFrameCocycle318.cocycle (pulled f U c) (fun a => f ⁻¹ᵁ U a) (fullFrames f U c) =
      UnitCocycleSchemeRefinement318.cocycle f U (fun a => f ⁻¹ᵁ U a) (fun _ => le_rfl) c := by
  have h := LinePullbackTransitions318.cocycle f (M U c) U
    (CocycleCanonicalTransitions318.frames U c)
  rw [CocycleCanonicalTransitions318.cocycle_eq] at h
  apply UnitTransitionCocycle318.Cocycle.ext
  intro a b
  have hh := congrArg (fun z => z.transition a b) h
  change LineFrameTransitions318.scalar (pulled f U c) (fun a => f ⁻¹ᵁ U a)
    (fullFrames f U c) a b (f ⁻¹ᵁ (U a ⊓ U b)) _ _ =
      Units.map (f.app (U a ⊓ U b)).hom.toMonoidHom (c.transition a b) at hh
  change LineFrameTransitions318.scalar (pulled f U c) (fun a => f ⁻¹ᵁ U a)
    (fullFrames f U c) a b ((f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b)) _ _ =
      Units.map (f.appLE (U a ⊓ U b) ((f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b)) _).hom.toMonoidHom _
  simpa only [← Scheme.Hom.preimage_inf, Scheme.Hom.appLE_eq_app] using hh
variable (V : ι → X.Opens) (hV : ∀ a, V a ≤ f ⁻¹ᵁ U a)
@[expose] def frames (a : ι) :
    SheafOfModules.unit (V a).toScheme.ringCatSheaf ≅ (pulled f U c).restrict (V a).ι :=
  OpenLineFrameRefinement318.refinedFrames (pulled f U c) (fun a => f ⁻¹ᵁ U a)
    (fullFrames f U c) V id hV a
lemma extracted :
    LineFrameCocycle318.cocycle (pulled f U c) V (frames f U c V hV) =
      UnitCocycleSchemeRefinement318.cocycle f U V hV c := by
  change LineFrameCocycle318.cocycle (pulled f U c) V
    (OpenLineFrameRefinement318.refinedFrames (pulled f U c) (fun a => f ⁻¹ᵁ U a)
      (fullFrames f U c) V id hV) = _
  rw [OpenLineFrameRefinement318.extracted_refine, full_cocycle,
    UnitCocycleSchemeRefinement318.refine_full]
/-- The original module-sheaf pullback is actually isomorphic to the original
coefficient-map cocycle line on ANY proved full-cover refinement. -/
@[expose] def iso (hc : (⊤ : X.Opens) ≤ ⨆ a, V a) :
    pulled f U c ≅ CocycleModule318.object V (UnitCocycleSchemeRefinement318.cocycle f U V hV c) :=
  CocycleEqualityTransport318.changeTarget V
    (LineFrameReconstructionIso318.iso (pulled f U c) V (frames f U c V hV) hc)
    (extracted f U c V hV)
lemma hom_coefficient (hc : (⊤ : X.Opens) ≤ ⨆ a, V a) (a : ι) :
    (iso f U c V hV hc).hom ≫ CocycleModule318.coefficient V
      (UnitCocycleSchemeRefinement318.cocycle f U V hV c) a =
      LineFrameAdjunction318.coordinate (pulled f U c) (V a) (frames f U c V hV a) := by
  rw [iso, CocycleEqualityTransport318.changeTarget_coefficient,
    LineFrameReconstructionIso318.hom_coefficient]
end OriginalCocyclePullbackLine318
