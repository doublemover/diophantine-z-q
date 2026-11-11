module
public import RigidifiedRestrictionComposition318
public section
noncomputable section
namespace OriginalOpenIsoGluing318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318 OpenSheafRestrictionCompatibility318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- Repeated original over-open restriction retains exactly the original
component maps; this is the actual normalization law, not a new premise. -/
lemma restrict_twice {X : Scheme.{u}} {M N : X.Modules} {U V W : X.Opens}
    (a : M.over U ≅ N.over U) (h : V ≤ U) (k : W ≤ V) :
    OpenSheafTransition318.restrictIso (OpenSheafTransition318.restrictIso a h) k =
      OpenSheafTransition318.restrictIso a (k.trans h) := by
  apply Iso.ext
  ext A s
  rfl

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u} (U : ι → X.Opens)
  (a : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
  (compatible : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
    schemeRestrict (a i) hi = schemeRestrict (a j) hj)

/-- The original scheme-local isomorphisms supply every actual subopen
linear map, with naturality and common-subopen equality derived through
the original restriction-to-over-open comparison. -/
@[expose] def data : ModuleLocalGluing318.LocalData M N U where
  map i V hi := (component (OpenChartModuleImages318.toOverIso (U i) (a i)) V hi).toLinearMap
  natural i V W hi h s := component_natural _ V W hi h s
  compatible i j V hi hj s := by
    have hh := congrArg (fun z => component (OpenChartModuleImages318.toOverIso V z) V le_rfl s)
      (compatible i j V hi hj)
    simpa only [restriction_compatible,component_restrict] using hh

/-- Actual global isomorphism between the unchanged original sheaves,
obtained by original full-subopen section gluing, not a replacement object. -/
@[expose] def iso (hc : (⊤ : X.Opens) ≤ iSup U) : M ≅ N :=
  ModuleLocalIsomorphism318.iso (data U a compatible) hc
    (fun i V hi => (component (OpenChartModuleImages318.toOverIso (U i) (a i)) V hi).bijective)
end OriginalOpenIsoGluing318
