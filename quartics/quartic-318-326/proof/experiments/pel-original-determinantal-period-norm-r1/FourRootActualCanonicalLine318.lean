module
public import FourRootWholeCanonicalCover318
public import ActualOpenImmersionLineFrame318
public section
noncomputable section
namespace FourRootActualCanonicalLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318 FourRootWholeCanonicalCover318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
@[expose] def opens(i:Option (Fin 4)):(scheme b).Opens:=(embedding b hb i).opensRange
lemma cover_top:(⊤:(scheme b).Opens)≤⨆i,opens b hb i:=by
  intro x _
  rcases frames_cover b hb x with ⟨i,q,hq⟩|⟨q,hq⟩
  · apply Opens.mem_iSup.mpr
    exact ⟨some i,q,hq⟩
  · apply Opens.mem_iSup.mpr
    exact ⟨none,q,hq⟩
@[expose] def frame(i:Option (Fin 4)):
    SheafOfModules.unit (opens b hb i).toScheme.ringCatSheaf≅
      (omega b).restrict (opens b hb i).ι:=
  ActualOpenImmersionLineFrame318.ambientFrame (embedding b hb i) (omega b)
    (localFrame b hb i).symm
/-- The genuine canonical line object has the original intrinsic Omega
as its object, with the produced covering frames on actual ambient opens. -/
@[expose] def canonicalLine:LineSheafClass318.Line (scheme b) where
  object:=omega b
  Index:=Option (Fin 4)
  opens:=opens b hb
  cover:=cover_top b hb
  frame:=frame b hb
@[simp] lemma canonicalLine_object:(canonicalLine b hb).object=omega b:=rfl
@[expose] def freeFrame(i:Option (Fin 4)):
    SheafOfModules.free (R:=(opens b hb i).toScheme.ringCatSheaf) PUnit≅
      (omega b).restrict (opens b hb i).ι:=
  coproductUniqueIso (fun _:PUnit=>SheafOfModules.unit (opens b hb i).toScheme.ringCatSheaf)
    ≪≫frame b hb i
/-- Bundled local freeness is proved from the same singleton free frames,
not installed as a hypothesis or inferred from closed-point dimensions. -/
theorem locallyFree:(omega b).IsLocallyFree:=
  ModuleFreeOpenFrames318.locallyFree (omega b) PUnit (opens b hb)
    (cover_top b hb) (freeFrame b hb)
end FourRootActualCanonicalLine318
