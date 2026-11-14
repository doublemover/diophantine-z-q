module
public import LineSheafClass318
public import AffineLineFrameCover318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace OriginalLineAffineModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L : Line X)

/-- Original rank-one frames on the full original cover prove genuine
local freeness of the actual module sheaf. -/
instance locallyFree : L.object.IsLocallyFree :=
  ModuleFreeOpenFrames318.locallyFree L.object PUnit.{u+1} L.opens L.cover
    (fun i => coproductUniqueIso
      (fun _ : PUnit.{u+1} => SheafOfModules.unit (L.opens i).toScheme.ringCatSheaf) ≪≫ L.frame i)

instance quasicoherent : L.object.IsQuasicoherent := inferInstance

variable (R : CommRingCat.{u}) (N : Line (Spec R))
/-- The original global section module with its original structural R action. -/
abbrev sections := moduleSpecΓFunctor.obj N.object

/-- The actual canonical tilde-Gamma counit, not an unrelated module model. -/
@[expose] def canonicalIso : tilde (sections R N) ≅ N.object := asIso N.object.fromTildeΓ

lemma canonicalIso_hom : (canonicalIso R N).hom = N.object.fromTildeΓ := rfl

/-- Existing original principal-frame arguments retain finite presentation,
flatness and rank one at every actual prime for exactly these sections. -/
lemma properties : Module.FinitePresentation R (sections R N) ∧
    Module.Flat R (sections R N) ∧
    ∀ q : PrimeSpectrum R, Module.rankAtStalk (sections R N) q = 1 :=
  AffineLineFrameCover318.properties R N.object N.opens N.cover N.frame
end OriginalLineAffineModel318
