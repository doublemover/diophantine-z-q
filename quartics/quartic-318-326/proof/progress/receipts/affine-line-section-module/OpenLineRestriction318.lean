module
public import OpenLineSectionBasis318
public section
noncomputable section
namespace OpenLineRestriction318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsOpenImmersion f] (M:Y.Modules) (V:Y.Opens)
    (e:SheafOfModules.unit (V:Scheme).ringCatSheaf≅M.restrict V.ι)
/-- Pull back the original line frame to the actual inverse-image open. -/
@[expose] def frame:SheafOfModules.unit ((f⁻¹ᵁV):Scheme).ringCatSheaf≅
    (M.restrict f).restrict (f⁻¹ᵁV).ι:=by
  let g:=f.resLE V (f⁻¹ᵁV) le_rfl
  letI:IsOpenImmersion g:=by dsimp [g];rw [Scheme.Hom.resLE_eq_morphismRestrict];infer_instance
  exact (Scheme.Modules.restrictUnitIso g).symm ≪≫
    (Scheme.Modules.restrictFunctor g).mapIso e ≪≫
      ((Scheme.Modules.restrictFunctorComp g V.ι).symm.app M) ≪≫
        ((Scheme.Modules.restrictFunctorCongr (f.resLE_comp_ι le_rfl)).app M) ≪≫
          ((Scheme.Modules.restrictFunctorComp (f⁻¹ᵁV).ι f).app M)
variable {κ:Type u} (V':κ→Y.Opens) (hc:(⊤:Y.Opens)≤⨆i,V' i)
include hc in
lemma covers:(⊤:X.Opens)≤⨆i,f⁻¹ᵁV' i:=by
  intro x _
  obtain ⟨i,hi⟩:=Opens.mem_iSup.mp (hc (show f x∈(⊤:Y.Opens) from trivial))
  exact Opens.mem_iSup.mpr ⟨i,hi⟩
end OpenLineRestriction318
