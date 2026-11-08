module
public import OpenLineFrameRefinement318
public import LineFrameChartCoordinates318
public section
noncomputable section
namespace OpenFrameRestrictionComparison318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (W:X.Opens) (h:W≤U)
lemma image_eq (Z:W.toScheme.Opens):
    U.ι ''ᵁ((X.homOfLE h) ''ᵁZ)=W.ι ''ᵁZ:=by
  rw [←Scheme.Hom.comp_image,Scheme.homOfLE_ι]
lemma original_formula (Z:W.toScheme.Opens) (s:Γ(W.toScheme,Z)):
    (OpenLineSectionBasis318.restrictFrame M U e W h).hom.val.app (op Z) s=
      M.presheaf.map (homOfLE (image_eq U W h Z).symm.le).op
        (e.hom.val.app (op ((X.homOfLE h) ''ᵁZ)) ((X.homOfLE h).appIso Z |>.inv <| s)):=by
  simp only [OpenLineSectionBasis318.restrictFrame,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom]
  rfl
end OpenFrameRestrictionComparison318
