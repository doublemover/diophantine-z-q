module
public import FiniteLineTargetCover318
public import FifthChartNorm318
public section
noncomputable section
namespace FifthLineTargetCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
variable (M:Model.Modules) {κ:Type} (V:κ→Model.Opens)
    (hc:(⊤:Model.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
/-- The actual fifth quotient's target cover for this unchanged source line. -/
abbrev neighborhood:=FiniteLineTargetCover318.neighborhood map M V hc frames
lemma cover_top:(⊤:Target.Opens)≤⨆y,neighborhood M V hc frames y:=
  FiniteLineTargetCover318.cover_top map M V hc frames
lemma preimage_cover_top:(⊤:Model.Opens)≤⨆y,map⁻¹ᵁneighborhood M V hc frames y:=
  FiniteLineTargetCover318.preimage_cover_top map M V hc frames
@[expose] def frame (y:Target):
    SheafOfModules.unit (map⁻¹ᵁneighborhood M V hc frames y).toScheme.ringCatSheaf≅
      M.restrict (map⁻¹ᵁneighborhood M V hc frames y).ι:=
  FiniteLineTargetCover318.frame map M V hc frames y
lemma mem_neighborhood (y:Target):y∈neighborhood M V hc frames y:=
  FiniteLineTargetCover318.mem_neighborhood map M V hc frames y
lemma affine_neighborhood (y:Target):IsAffineOpen (neighborhood M V hc frames y):=
  FiniteLineTargetCover318.affine_neighborhood map M V hc frames y
end FifthLineTargetCover318
