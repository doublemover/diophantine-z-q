module
public import PullbackLineFrames318
public import PullbackChartNaturality318
public section
noncomputable section
namespace LinePullbackFrames318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U:Y.Opens)
@[expose] def chartMap:(f⁻¹ᵁU).toScheme⟶U.toScheme:=f.resLE U (f⁻¹ᵁU) le_rfl
lemma square:(f⁻¹ᵁU).ι≫f=chartMap f U≫U.ι:=(f.resLE_comp_ι le_rfl).symm
/-- A genuine frame of the actual module-sheaf pullback over the entire
inverse image of the original target open. No flatness hypothesis is used. -/
@[expose] def frame (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    SheafOfModules.unit (f⁻¹ᵁU).toScheme.ringCatSheaf≅
      ((Scheme.Modules.pullback f).obj M).restrict (f⁻¹ᵁU).ι:=
  (PullbackLineFrames318.frame f U.ι (f⁻¹ᵁU).ι (chartMap f U) (square f U) M e.symm).symm
lemma hom_inv (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    (frame f M U e).hom≫(frame f M U e).inv=𝟙 _ :=(frame f M U e).hom_inv_id
lemma inv_hom (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    (frame f M U e).inv≫(frame f M U e).hom=𝟙 _ :=(frame f M U e).inv_hom_id
/-- The same original pullback, chart comparison and unit comparison remain
visible in the actual inverse frame; this is not an abstract local iso. -/
lemma inverse_formula (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    (frame f M U e).inv=
      (PullbackLineFrames318.chartIso f U.ι (f⁻¹ᵁU).ι (chartMap f U) (square f U) M).hom≫
        (Scheme.Modules.pullback (chartMap f U)).map e.inv≫
        (IdentityCotangent318.pullbackUnitIso (chartMap f U)).hom:=rfl
lemma preimage_cover {ι:Type u} (V:ι→Y.Opens) (hc:(⊤:Y.Opens)≤⨆i,V i):
    (⊤:X.Opens)≤⨆i,f⁻¹ᵁV i:=by
  have h:=f.preimage_mono hc
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.preimage_iSup] using h
end LinePullbackFrames318
