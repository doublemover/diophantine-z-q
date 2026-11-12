module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public section
noncomputable section
namespace ModuleFreeOpenFrames318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens) (ι:Type u)
    (e:SheafOfModules.free (R:=(U:Scheme).ringCatSheaf) ι≅M.restrict U.ι)
/-- The same actual open frame on the site-over-open model, through the
canonical equivalence with module sheaves on the open subscheme. -/
@[expose] def overFrame:SheafOfModules.free (R:=X.ringCatSheaf.over U) ι≅M.over U:=by
  let E:=Scheme.Modules.overEquiv U
  exact E.functor.preimageIso <|
    (SheafOfModules.mapFreeIso E.functor ι
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).symm ≪≫
      e ≪≫ ((Scheme.Modules.overFunctorEquiv U).app M).symm
variable {κ:Type u} (V:κ→X.Opens) (hc:(⊤:X.Opens)≤⨆ i,V i)
    (frames:∀i,SheafOfModules.free (R:=((V i):Scheme).ringCatSheaf) ι≅M.restrict (V i).ι)
/-- Genuine local generating sections, obtained from the original free-sheaf
frames rather than merely from a dimension or section-module rank. -/
@[expose] def data:M.LocalGeneratorsData where
  I:=κ
  X:=V
  coversTop:=(Opens.coversTop_iff X V).mpr (show IsOpenCover V from le_antisymm le_top hc)
  generators i:=(SheafOfModules.free.generatingSections ι).ofEpi
    (overFrame M (V i) ι (frames i)).hom
lemma frame_generators_iso {C:Type u} [Category C] {J:GrothendieckTopology C}
    {R:Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {N:SheafOfModules R} {I:Type u} (g:SheafOfModules.free I≅N):
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi g.hom).π:=by
  rw [SheafOfModules.GeneratingSections.ofEpi_π,SheafOfModules.free.generatingSections_π]
  change IsIso ((𝟙 (SheafOfModules.free I))≫g.hom)
  infer_instance
lemma data_free:(data M ι V hc frames).IsLocallyFreeData where
  isIso i:=frame_generators_iso (overFrame M (V i) ι (frames i))
include hc frames
/-- A covering family of actual O-module-sheaf frames proves bundled local
freeness. The number of generators is retained explicitly in data. -/
lemma locallyFree:M.IsLocallyFree:=by
  letI:=data_free M ι V hc frames
  exact (data M ι V hc frames).isLocallyFree
end ModuleFreeOpenFrames318
