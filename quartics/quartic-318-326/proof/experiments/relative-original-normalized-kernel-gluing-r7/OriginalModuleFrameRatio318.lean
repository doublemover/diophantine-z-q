module
public import OriginalChartFrameUnitPullback318
public section
noncomputable section
namespace OriginalModuleFrameRatio318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M : X.Modules}
  (e d : SheafOfModules.unit X.ringCatSheaf ≅ M)
/-- Ratio of actual frames of ANY module already supplied with these
frames. No new Line presentation, basis choice or inhabitance is added. -/
@[expose] def ratio : Γ(X,⊤)ˣ := StructureLineAutomorphisms318.value X (d ≪≫ e.symm)
lemma action : StructureLineAutomorphisms318.iso X (ratio e d) ≪≫ e=d := by
  rw [ratio,StructureLineAutomorphisms318.value_iso]
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
end OriginalModuleFrameRatio318
