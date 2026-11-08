module
public import CocycleModuleCone318
public import UnitCocycleSubopens318
public section
noncomputable section
namespace CocycleLocalCoefficients318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
@[expose] def localChart (i j:ι):(U i).toScheme.Modules:=
  (CocycleModule318.chart U j).restrict (U i).ι
lemma ambient_open (i j:ι):
    (U j).ι ''ᵁ ((U j).ι⁻¹ᵁ((U i).ι ''ᵁ ⊤))=U j⊓U i:=by
  rw [Scheme.Opens.ι_image_top,Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
/-- The actual top sections of a restricted chart are the original ambient
sections on the complete intersection, retaining their ring multiplication. -/
@[expose] def coefficientIso (i j:ι):
    Γ((U j).toScheme,(U j).ι⁻¹ᵁ((U i).ι ''ᵁ ⊤))≅Γ(X,U j⊓U i):=
  X.presheaf.mapIso (eqToIso (ambient_open U i j).symm).op
/-- The original reversed transition determines the actual j-th coefficient
of the inverse i-frame. No inverse sign convention is chosen abstractly. -/
@[expose] def localSection (i j:ι):Γ(localChart U i j,⊤):=
  (coefficientIso U i j).inv (c.transition j i).val
@[expose] def localMap (i j:ι):ClutchedModule318.unit (U i).toScheme⟶localChart U i j:=
  ModuleGlobalSections318.ofTop (localChart U i j) (localSection U c i j)
lemma localMap_one (i j:ι):
    (localMap U c i j).app ⊤ (1:Γ((U i).toScheme,⊤))=localSection U c i j:=by
  have h:=ModuleGlobalSections318.ofTop_one (localChart U i j) (localSection U c i j) ⊤
  change (localMap U c i j).app ⊤ (1:Γ((U i).toScheme,⊤))=_ at h
  change (localMap U c i j).app ⊤ (1:Γ((U i).toScheme,⊤))=
    (localChart U i j).presheaf.map (𝟙 (op ⊤)) (localSection U c i j) at h
  exact h.trans (congrArg
    (fun f : (localChart U i j).presheaf.obj (op ⊤) ⟶
      (localChart U i j).presheaf.obj (op ⊤) => f (localSection U c i j))
    ((localChart U i j).presheaf.map_id (op ⊤)))
end CocycleLocalCoefficients318
