module
public import OriginalTensorUnitFrameAction318
public section
noncomputable section
namespace OriginalChartFrameUnitPullback318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
/-- Native chart-frame pullback transports the actual chart unit through
the WHOLE chart map, retaining the original unit and chart comparisons. -/
lemma action (a : Γ(U.toScheme,⊤)ˣ) :
    LinePullbackFrames318.frame p M U
      (StructureLineAutomorphisms318.iso U.toScheme a ≪≫ e)=
    StructureLineAutomorphisms318.iso (p ⁻¹ᵁ U).toScheme
      (OriginalFramePullbackUnits318.units (LinePullbackFrames318.chartMap p U) a) ≪≫
        LinePullbackFrames318.frame p M U e := by
  apply Iso.ext
  change (IdentityCotangent318.pullbackUnitIso (LinePullbackFrames318.chartMap p U)).inv ≫
    (Scheme.Modules.pullback (LinePullbackFrames318.chartMap p U)).map
      ((ClutchedModule318.multiply (a:Γ(U.toScheme,⊤))) ≫ e.hom) ≫ _=_
  rw [Functor.map_comp,←Category.assoc,
    OriginalFramePullbackUnits318.unit_inverse_square]
  simp only [Category.assoc]
end OriginalChartFrameUnitPullback318
