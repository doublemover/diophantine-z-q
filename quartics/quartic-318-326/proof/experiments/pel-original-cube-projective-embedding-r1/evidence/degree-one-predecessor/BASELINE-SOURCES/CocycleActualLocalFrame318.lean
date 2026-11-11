module
public import CocycleLocalLift318
public import ModuleFreeOpenFrames318
public section
noncomputable section
namespace CocycleActualLocalFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CocycleLocalCoefficients318 CocycleOverlapCoordinates318 CocycleLocalFamily318 CocycleLocalLift318
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
@[expose] def projection (i j:ι):
    (CocycleModule318.object U c).restrict (U i).ι⟶localChart U i j:=
  (restriction U i).map (CocycleModule318.coefficient U c j)
lemma projection_compatible (i j k:ι):
    projection U c i j≫localLeft U i j k=projection U c i k≫localRight U c i j k:=by
  have h:=congrArg (fun f=>(restriction U i).map f) (CocycleModule318.compatible U c j k)
  simpa only [projection,localLeft,localRight,restriction,Functor.map_comp] using h
instance left_iso (i j:ι):IsIso (localLeft U i j i):=
  ClutchedModuleFrames318.restriction_isIso (U i).ι (U j).ι
    (OpenClutchedLine318.leftInclusion (U j) (U i))
    (OpenClutchedLine318.left_range (U j) (U i))
/-- The inverse of the exact restricted i-th coefficient map. -/
@[expose] def projectionInverse (i:ι):localChart U i i⟶
    (CocycleModule318.object U c).restrict (U i).ι:=
  inv (localMap U c i i)≫localLift U c i
lemma inverse_projection (i:ι):projectionInverse U c i≫projection U c i i=𝟙 _:=by
  simp only [projectionInverse,projection,Category.assoc,localLift_coefficient,IsIso.inv_hom_id]
lemma projection_inverse (i:ι):projection U c i i≫projectionInverse U c i=𝟙 _:=by
  apply restricted_hom_ext U c i
  intro j
  change (projection U c i i≫projectionInverse U c i)≫projection U c i j=
    (𝟙 _)≫projection U c i j
  simp only [projectionInverse,Category.assoc,Category.id_comp]
  rw [show localLift U c i≫projection U c i j=localMap U c i j from localLift_coefficient U c i j]
  apply (cancel_mono (localLeft U i j i)).mp
  calc
    (projection U c i i≫inv (localMap U c i i)≫localMap U c i j)≫localLeft U i j i=
      projection U c i i≫inv (localMap U c i i)≫(localMap U c i j≫localLeft U i j i):=by simp only [Category.assoc]
    _=projection U c i i≫inv (localMap U c i i)≫(localMap U c i i≫localRight U c i j i):=by
      rw [CocycleLocalFamily318.compatible]
    _=projection U c i i≫localRight U c i j i:=by simp only [IsIso.inv_hom_id_assoc]
    _=projection U c i j≫localLeft U i j i:=(projection_compatible U c i j i).symm
@[expose] def projectionIso (i:ι):
    (CocycleModule318.object U c).restrict (U i).ι≅localChart U i i where
  hom:=projection U c i i
  inv:=projectionInverse U c i
  hom_inv_id:=projection_inverse U c i
  inv_hom_id:=inverse_projection U c i
instance projection_iso (i:ι):IsIso (projection U c i i):=(projectionIso U c i).isIso_hom
/-- The exact adjunction transpose of the original coefficient morphism. -/
@[expose] def transpose (i:ι):
    (CocycleModule318.object U c).restrict (U i).ι⟶ClutchedModule318.unit (U i).toScheme:=
  ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv
    (CocycleModule318.object U c) (ClutchedModule318.unit (U i).toScheme)).symm
      (CocycleModule318.coefficient U c i)
lemma transpose_eq (i:ι):transpose U c i=projection U c i i≫counit U i:=
  (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv_counit _ _ _
instance transpose_iso (i:ι):IsIso (transpose U c i):=by
  rw [transpose_eq]
  infer_instance
/-- Genuine frame of the actual cocycle sheaf on each original chart,
with the actual coefficient transpose as its forward map. -/
@[expose] def frame (i:ι):
    (CocycleModule318.object U c).restrict (U i).ι≅ClutchedModule318.unit (U i).toScheme:=
  asIso (transpose U c i)
lemma frame_hom (i:ι):(frame U c i).hom=transpose U c i:=rfl
lemma frame_hom_inv (i:ι):(frame U c i).hom≫(frame U c i).inv=𝟙 _ :=(frame U c i).hom_inv_id
lemma frame_inv_hom (i:ι):(frame U c i).inv≫(frame U c i).hom=𝟙 _ :=(frame U c i).inv_hom_id
variable (hc:(⊤:X.Opens)≤⨆i,U i)
include hc in
lemma locallyFree:(CocycleModule318.object U c).IsLocallyFree:=
  ModuleFreeOpenFrames318.locallyFree (CocycleModule318.object U c) PUnit.{u+1} U hc
    (fun i=>coproductUniqueIso (fun _:PUnit.{u+1}=>ClutchedModule318.unit (U i).toScheme) ≪≫
      (frame U c i).symm)
end CocycleActualLocalFrame318
