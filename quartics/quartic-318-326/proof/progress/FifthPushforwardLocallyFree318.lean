module
public import FifthPrincipalNeighborhood318
public import AffinePushforwardFrame318
public import ModuleFreeOpenFrames318
public import FifthPushforwardModule318
public section
noncomputable section
namespace FifthPushforwardLocallyFree318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance sectionAlgebra (U:Target.Opens):Algebra Γ(Target,U) Γ(Model,map⁻¹ᵁU):=(map.app U).hom.toAlgebra
abbrev object:Target.Modules:=FifthPushforwardModule318.object
structure Neighborhood (x:Target) where
  chart:Bool
  parameter:Γ(Target,chartOpen chart)
  mem:x∈Target.basicOpen parameter
  basis:Module.Basis (Fin 8) Γ(Target,Target.basicOpen parameter)
    Γ(Model,map⁻¹ᵁTarget.basicOpen parameter)
@[expose] def neighborhood (x:Target):Neighborhood x:=Classical.choice (by
  obtain ⟨b,r,hx,⟨bs⟩⟩:=FifthPrincipalNeighborhood318.cover x
  exact ⟨⟨b,r,hx,bs⟩⟩)
@[expose] def openAt (x:Target):Target.Opens:=Target.basicOpen (neighborhood x).parameter
lemma affineAt (x:Target):IsAffineOpen (openAt x):=
  (chart_affine (neighborhood x).chart).basicOpen (neighborhood x).parameter
lemma covers:(⊤:Target.Opens)≤⨆x:Target,openAt x:=by
  intro x hx
  exact Opens.mem_iSup.mpr ⟨x,(neighborhood x).mem⟩
/-- Actual rank-eight free module-sheaf frame on a principal neighborhood
of every original target point, with explicit inverse maps. -/
@[expose] def frame (x:Target):
    SheafOfModules.free (R:=((openAt x):Scheme).ringCatSheaf) (Fin 8)≅object.restrict (openAt x).ι:=
  AffinePushforwardFrame318.frame map (openAt x) (affineAt x) (neighborhood x).basis
lemma frame_hom_inv (x:Target):(frame x).hom≫(frame x).inv=𝟙 _ :=(frame x).hom_inv_id
lemma frame_inv_hom (x:Target):(frame x).inv≫(frame x).hom=𝟙 _ :=(frame x).inv_hom_id
/-- The original pushforward's actual fixed-eight local generators. -/
@[expose] def data:object.LocalGeneratorsData:=
  ModuleFreeOpenFrames318.data object (Fin 8) openAt covers frame
lemma data_free:data.IsLocallyFreeData:=
  ModuleFreeOpenFrames318.data_free object (Fin 8) openAt covers frame
lemma generator_index (x:Target):(data.generators x).I=Fin 8:=rfl
/-- Bundled local freeness of the genuine original O-module pushforward. -/
lemma locallyFree:object.IsLocallyFree:=
  ModuleFreeOpenFrames318.locallyFree object (Fin 8) openAt covers frame
end FifthPushforwardLocallyFree318
