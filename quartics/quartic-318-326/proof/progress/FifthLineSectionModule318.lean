module
public import AffineLineSections318
public import FifthChartNorm318
public section
noncomputable section
namespace FifthLineSectionModule318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
variable (M:Model.Modules) {κ:Type} (V:κ→Model.Opens)
    (hc:(⊤:Model.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
@[expose] def sectionEquiv (b:Bool):
    moduleSpecΓFunctor.obj (M.restrict ((chart_affine b).preimage map).fromSpec)≃ₗ[
      Γ(Model,map⁻¹ᵁchartOpen b)]Γ(M,map⁻¹ᵁchartOpen b):=
  AffineModuleSectionEquiv318.equiv M (map⁻¹ᵁchartOpen b) ((chart_affine b).preimage map)
include hc frames in
/-- Exact missing hypotheses on the whole affine inverse-image chart for
any genuine source line with supplied covering singleton frames. -/
lemma properties (b:Bool):
    Module.FinitePresentation Γ(Model,map⁻¹ᵁchartOpen b) Γ(M,map⁻¹ᵁchartOpen b) ∧
    Module.Flat Γ(Model,map⁻¹ᵁchartOpen b) Γ(M,map⁻¹ᵁchartOpen b) ∧
    ∀p:PrimeSpectrum Γ(Model,map⁻¹ᵁchartOpen b),
      Module.rankAtStalk Γ(M,map⁻¹ᵁchartOpen b) p=1:=
  AffineLineSections318.properties M (map⁻¹ᵁchartOpen b)
    ((chart_affine b).preimage map) V hc frames
end FifthLineSectionModule318
