module
public import AffineLineModule318
public section
noncomputable section
namespace AffineLineFrameCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R:CommRingCat.{u}) (M:(Spec R).Modules)
variable {κ:Type u} (V:κ→(Spec R).Opens) (hc:(⊤:(Spec R).Opens)≤⨆i,V i)
  (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
@[expose] def freeFrames (i:κ):
    SheafOfModules.free (R:=((V i):Scheme).ringCatSheaf) PUnit.{u+1}≅M.restrict (V i).ι:=
  coproductUniqueIso (fun _:PUnit.{u+1}=>SheafOfModules.unit ((V i):Scheme).ringCatSheaf) ≪≫ frames i
include hc frames in
lemma locallyFree:M.IsLocallyFree:=
  ModuleFreeOpenFrames318.locallyFree M PUnit.{u+1} V hc (freeFrames R M V frames)
include hc frames in
/-- Refine the original covering line frames to genuine principal frames,
without assuming a single affine trivialization. -/
lemma principalCover (p:PrimeSpectrum R):
    ∃r:R,r∉p.asIdeal ∧ r∈AffineLineModule318.frameSet R M:=by
  obtain ⟨i,hi⟩:=Opens.mem_iSup.mp (hc (show p∈(⊤:(Spec R).Opens) from trivial))
  obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hpr,hrV:PrimeSpectrum.basicOpen _≤_⟩:=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hi (V i).isOpen
  exact ⟨r,hpr,⟨OpenLineSectionBasis318.restrictFrame M (V i) (frames i)
    (AffineLineModule318.basic R r) hrV⟩⟩
include hc frames in
/-- A genuine line sheaf on the original affine Scheme yields a finitely
presented flat rank-one original global section module. -/
lemma properties:Module.FinitePresentation R (AffineLineModule318.globals R M) ∧
    Module.Flat R (AffineLineModule318.globals R M) ∧
    ∀p:PrimeSpectrum R,Module.rankAtStalk (AffineLineModule318.globals R M) p=1:=by
  letI:=locallyFree R M V hc frames
  exact ⟨AffineLineModule318.finitePresentation R M (principalCover R M V hc frames),
    AffineLineModule318.flat R M (principalCover R M V hc frames),
    AffineLineModule318.rank_one R M (principalCover R M V hc frames)⟩
end AffineLineFrameCover318
