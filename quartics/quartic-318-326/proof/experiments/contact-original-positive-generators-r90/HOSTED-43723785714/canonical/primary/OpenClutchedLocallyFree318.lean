module
public import OpenClutchedLine318
public import ModuleFreeOpenFrames318
public section
noncomputable section
namespace OpenClutchedLocallyFree318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OpenClutchedLine318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
@[expose] def freeUnit (X:Scheme.{u}):
    SheafOfModules.free (R:=X.ringCatSheaf) PUnit.{u+1}≅ClutchedModule318.unit X:=
  coproductUniqueIso (fun _:PUnit.{u+1}=>ClutchedModule318.unit X)
variable {X:Scheme.{u}} (U V:X.Opens) (a:Γ(X,U⊓V)ˣ) (hc:U⊔V=⊤)
@[expose] def cover:ULift.{u} Bool→X.Opens:=fun b=>if b.down then V else U
include hc in
lemma cover_top:⊤ ≤ iSup (cover U V):=by
  intro x _
  have hx:x∈U⊔V:=by rw [hc];trivial
  rcases hx with hx|hx
  · exact Opens.mem_iSup.mpr ⟨⟨false⟩,hx⟩
  · exact Opens.mem_iSup.mpr ⟨⟨true⟩,hx⟩
@[expose] def frame (b:ULift.{u} Bool):
    SheafOfModules.free (R:=((cover U V b):Scheme).ringCatSheaf) PUnit.{u+1}≅
      (line U V a).restrict (cover U V b).ι:=by
  rcases b with ⟨b⟩
  cases b
  · exact freeUnit U.toScheme≪≫(firstFrame U V a).symm
  · exact freeUnit V.toScheme≪≫(secondFrame U V a).symm
/-- Actual local generator data with a singleton indexing set on every
member of the original two-open cover. -/
@[expose] def data:(line U V a).LocalGeneratorsData:=
  ModuleFreeOpenFrames318.data (line U V a) PUnit.{u+1} (cover U V)
    (cover_top U V hc) (frame U V a)
lemma data_free:(data U V a hc).IsLocallyFreeData:=
  ModuleFreeOpenFrames318.data_free (line U V a) PUnit.{u+1} (cover U V)
    (cover_top U V hc) (frame U V a)
include hc in
lemma locallyFree:(line U V a).IsLocallyFree:=
  ModuleFreeOpenFrames318.locallyFree (line U V a) PUnit.{u+1} (cover U V)
    (cover_top U V hc) (frame U V a)
end OpenClutchedLocallyFree318
