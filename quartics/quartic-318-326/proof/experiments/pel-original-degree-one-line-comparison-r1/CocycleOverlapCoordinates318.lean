module
public import CocycleLocalCoefficients318
public section
noncomputable section
namespace CocycleOverlapCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CocycleLocalCoefficients318
set_option maxHeartbeats 450000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
@[expose] def localOverlap (i j k:ι):(U i).toScheme.Modules:=
  (CocycleModule318.overlap U j k).restrict (U i).ι
lemma ambient_overlap (i j k:ι):
    (U j⊓U k:X.Opens).ι ''ᵁ
      ((OpenClutchedLine318.leftInclusion (U j) (U k)≫(U j).ι)⁻¹ᵁ((U i).ι ''ᵁ ⊤))=
      (U j⊓U k)⊓U i:=by
  simp only [OpenClutchedLine318.leftInclusion,Scheme.homOfLE_ι,
    Scheme.Opens.ι_image_top,Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
@[expose] def overlapIso (i j k:ι):
    Γ((U j⊓U k:X.Opens).toScheme,
      (OpenClutchedLine318.leftInclusion (U j) (U k)≫(U j).ι)⁻¹ᵁ((U i).ι ''ᵁ ⊤))≅
      Γ(X,(U j⊓U k)⊓U i):=
  X.presheaf.mapIso (eqToIso (ambient_overlap U i j k).symm).op
@[expose] def localLeft (i j k:ι):localChart U i j⟶localOverlap U i j k:=
  (Scheme.Modules.restrictFunctor (U i).ι).map (CocycleModule318.left U j k)
@[expose] def localRight (i j k:ι):localChart U i k⟶localOverlap U i j k:=
  (Scheme.Modules.restrictFunctor (U i).ι).map (CocycleModule318.right U c j k)
lemma left_coordinate (i j k:ι) (a:Γ(X,U j⊓U i)):
    (overlapIso U i j k).hom ((localLeft U i j k).app ⊤ ((coefficientIso U i j).inv a))=
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op a:=by
  change (overlapIso U i j k).hom
    ((OpenClutchedLine318.leftInclusion (U j) (U k)).app
      ((U j).ι⁻¹ᵁ((U i).ι ''ᵁ ⊤)) ((coefficientIso U i j).inv a))=_
  simp only [overlapIso,coefficientIso,Functor.mapIso_hom,Functor.mapIso_inv,
    OpenClutchedLine318.leftInclusion,Scheme.homOfLE_app]
  change ((X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) a=_
  simp only [←Functor.map_comp]
  rfl
end CocycleOverlapCoordinates318
