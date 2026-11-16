module
public import OriginalLineTensorInverseComposition318
public import PullbackUnitComposition318
public section
noncomputable section
namespace OriginalPulledCancellationComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}}
@[expose] def pull (f : X ⟶ Y) (L N : Line Y)
    (c : (LineSheafTensor318.line L N).object ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (LineSheafTensor318.line (LineSheafPullback318.line f L)
      (LineSheafPullback318.line f N)).object ≅ SheafOfModules.unit X.ringCatSheaf :=
  (LineClassPullbackHom318.tensorIso f L N).symm ≪≫
    (Scheme.Modules.pullback f).mapIso c ≪≫ IdentityCotangent318.pullbackUnitIso f
/-- Native pullback of ANY specified actual cancellation composes
through the exact tensor and unit comparisons. No newly chosen inverse
line or duality triangle is substituted. -/
lemma composition (f : X ⟶ Y) (g : Y ⟶ Z) (L N : Line Z)
    (c : (LineSheafTensor318.line L N).object ≅ SheafOfModules.unit Z.ringCatSheaf) :
    TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app L.object)
      ((Scheme.Modules.pullbackComp f g).app N.object) ≪≫ pull (f ≫ g) L N c=
    pull f (LineSheafPullback318.line g L) (LineSheafPullback318.line g N) (pull g L N c) := by
  have hi := congrArg Iso.hom (OriginalLineTensorInverseComposition318.square f g L N)
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality c.hom
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map c.hom) ≫
      (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf)=
    (Scheme.Modules.pullbackComp f g).hom.app (LineSheafTensor318.line L N).object ≫
      (Scheme.Modules.pullback (f ≫ g)).map c.hom at hn
  have hu := PullbackUnitComposition318.composition f g
  have hc : (Scheme.Modules.pullbackComp f g).hom.app (LineSheafTensor318.line L N).object ≫
      (Scheme.Modules.pullback (f ≫ g)).map c.hom ≫
      (IdentityCotangent318.pullbackUnitIso (f ≫ g)).hom=
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map c.hom) ≫
      (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).hom ≫
      (IdentityCotangent318.pullbackUnitIso f).hom := by
    rw [←Category.assoc,←hn,Category.assoc,hu]
  apply Iso.ext
  simp only [pull,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Functor.mapIso_inv,
    Functor.map_comp,Category.assoc] at hi ⊢
  rw [←Category.assoc _ (LineClassPullbackHom318.tensorIso (f ≫ g) L N).inv,hi]
  simp only [Category.assoc]
  rw [hc]
end OriginalPulledCancellationComposition318
