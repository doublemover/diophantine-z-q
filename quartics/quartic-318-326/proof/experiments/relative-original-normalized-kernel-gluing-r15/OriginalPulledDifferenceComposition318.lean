module
public import OriginalTensorConjugation318
public section
noncomputable section
namespace OriginalPulledDifferenceComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L K : Line Z)
local notation "I" => FramedLineInverse318.inverse L
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
/-- Pull the actual full line isomorphism and transport through the
native coefficient associators, retaining both original line objects. -/
@[expose] def pullIso
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object) :
    (LineSheafPullback318.line (f ≫ g) L).object ≅
      (LineSheafPullback318.line (f ≫ g) K).object :=
  ((Scheme.Modules.pullbackComp f g).app L.object).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ (Scheme.Modules.pullbackComp f g).app K.object
/-- The SPECIFIC old difference-frame map commutes with coefficient
composition, on arbitrary full isomorphisms, through native pullback and
its actual associator. No frame chosen only by torsor existence is used. -/
lemma frameOfIso
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object) :
    OriginalFramePullback318.frame f (LineSheafPullback318.line g D)
      (OriginalPulledDifferenceFrameWitness318.frameOfIso g L K e) ≪≫
      (Scheme.Modules.pullbackComp f g).app D.object=
    OriginalPulledDifferenceFrameWitness318.frameOfIso (f ≫ g) L K (pullIso f g L K e) := by
  let aI := (Scheme.Modules.pullbackComp f g).app I.object
  let aL := (Scheme.Modules.pullbackComp f g).app L.object
  let aK := (Scheme.Modules.pullbackComp f g).app K.object
  let IL := TensorSheafFunctor318.congr aI aL
  let IK := TensorSheafFunctor318.congr aI aK
  have hl := OriginalTensorConjugation318.inverse_cancel IL
    (OriginalPulledDifferenceFrameWitness318.leftCancel (f ≫ g) L)
    (OriginalInverseLineCancellationCoherence318.iteratedLeft f g L)
    (OriginalInverseLineCancellationCoherence318.left f g L)
  have ht := congrArg Iso.hom (OriginalTensorConjugation318.square aI aL aK
    ((Scheme.Modules.pullback f).mapIso e))
  have hi := congrArg Iso.hom (OriginalLineTensorInverseComposition318.square f g I K)
  have hn := congrArg Iso.hom (OriginalLineTensorIsoNaturality318.natural f
    (LineSheafPullback318.line g I) (LineSheafPullback318.line g L)
    (LineSheafPullback318.line g I) (LineSheafPullback318.line g K) (Iso.refl _) e)
  have hid : (Scheme.Modules.pullback f).mapIso
      (Iso.refl (LineSheafPullback318.line g I).object)=
      Iso.refl ((Scheme.Modules.pullback f).obj (LineSheafPullback318.line g I).object) := by
    apply Iso.ext
    exact (Scheme.Modules.pullback f).map_id _
  rw [hid] at hn
  apply Iso.ext
  symm
  simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Functor.mapIso_inv] at ht hi hn
  change (OriginalPulledDifferenceFrameWitness318.leftCancel (f ≫ g) L).inv ≫
      (TensorSheafFunctor318.congr (Iso.refl ((Scheme.Modules.pullback (f ≫ g)).obj I.object))
        (pullIso f g L K e)).hom ≫ (LineClassPullbackHom318.tensorIso (f ≫ g) I K).inv=_
  rw [hl]
  simp only [Category.assoc]
  rw [←Category.assoc IL.hom,ht]
  simp only [Category.assoc]
  rw [←Category.assoc IK.hom,hi]
  simp only [OriginalInverseLineCancellationCoherence318.iteratedLeft,
    OriginalPulledCancellationComposition318.pull,Iso.trans_inv,Iso.symm_inv,
    Functor.mapIso_inv,Category.assoc]
  rw [←Category.assoc (LineClassPullbackHom318.tensorIso f
    (LineSheafPullback318.line g I) (LineSheafPullback318.line g L)).hom,←hn]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  simp only [OriginalFramePullback318.frame,OriginalPulledDifferenceFrameWitness318.frameOfIso,
    Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Functor.map_comp,Category.assoc]
end OriginalPulledDifferenceComposition318
