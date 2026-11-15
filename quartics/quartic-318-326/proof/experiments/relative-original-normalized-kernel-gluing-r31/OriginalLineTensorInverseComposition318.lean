module
public import OriginalLineTensorCoefficientComposition318
public section
noncomputable section
namespace OriginalLineTensorInverseComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L N : Line Z)
/-- Solve the actual coefficient tensor square for its inverse face.
All inverse maps remain native inverses of the old comparisons. -/
lemma square :
    TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app L.object)
      ((Scheme.Modules.pullbackComp f g).app N.object) ≪≫
      (LineClassPullbackHom318.tensorIso (f ≫ g) L N).symm=
    (LineClassPullbackHom318.tensorIso f (LineSheafPullback318.line g L)
      (LineSheafPullback318.line g N)).symm ≪≫
      ((Scheme.Modules.pullback f).mapIso (LineClassPullbackHom318.tensorIso g L N)).symm ≪≫
      (Scheme.Modules.pullbackComp f g).app (LineSheafTensor318.line L N).object := by
  have h := congrArg Iso.hom (OriginalLineTensorCoefficientComposition318.composition f g L N)
  have hh := congrArg (fun q => q ≫ (LineClassPullbackHom318.tensorIso (f ≫ g) L N).inv) h
  apply Iso.ext
  apply (cancel_epi (LineClassPullbackHom318.tensorIso f (LineSheafPullback318.line g L)
    (LineSheafPullback318.line g N)).hom).mp
  apply (cancel_epi ((Scheme.Modules.pullback f).mapIso
    (LineClassPullbackHom318.tensorIso g L N)).hom).mp
  simpa only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc,
    Iso.hom_inv_id,Category.comp_id,Category.id_comp] using hh
end OriginalLineTensorInverseComposition318
