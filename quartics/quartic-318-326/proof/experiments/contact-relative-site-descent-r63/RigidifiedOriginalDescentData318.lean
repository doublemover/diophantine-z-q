module
public import OriginalGlobalLineMapDescent318
public import PointedPullbackComposition318
public section
noncomputable section
namespace RigidifiedOriginalDescentData318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)

/-- Original descent data with a specified local section trivialization.
The sole additional condition is its actual original double-overlap square
on the base cover. No global trivialization or class equality is supplied. -/
structure Datum where
  underlying : OriginalSchemeDescentData318.Datum f
  trivialization : (Scheme.Modules.pullback e').obj underlying.line.object ≅
    (LineSheafUnit318.line S').object
  commutes :
    (OriginalSchemeDescentBaseChange318.datum f g e' e square underlying).overlap ≫
        (Scheme.Modules.pullback (second g)).map
          (trivialization.hom ≫ (IdentityCotangent318.pullbackUnitIso g).inv) =
      (Scheme.Modules.pullback (first g)).map
          (trivialization.hom ≫ (IdentityCotangent318.pullbackUnitIso g).inv) ≫
        (OriginalCanonicalDescent318.datum g (LineSheafUnit318.line S)).overlap

variable (D : Datum f g e e' square)

@[expose] def localLine : RigidifiedLine e' where
  line := D.underlying.line
  trivialization := D.trivialization

@[expose] def trivializationHom : Hom
    (OriginalSchemeDescentBaseChange318.datum f g e' e square D.underlying)
    (OriginalCanonicalDescent318.datum g (LineSheafUnit318.line S)) where
  sheafHom := D.trivialization.hom ≫ (IdentityCotangent318.pullbackUnitIso g).inv
  commutes := D.commutes

lemma pointedComparison_eq :
    RigidifiedPointedPullback318.restrictionComparison e e' f g square =
      coverComparison f g e' e square :=
  PointedPullbackComposition318.restrictionComparison_eq e e' f g square

variable [IsAffineHom f] [Flat f] [Surjective f]

abbrev reconstructed := AffineMorphismGlobalEffectivity318.line f D.underlying

/-- The original reconstructed comparison transports the supplied local
trivialization to an actual compatible map between canonical base-cover data. -/
@[expose] def coveringHom : Hom
    (OriginalCanonicalDescent318.datum g
      (LineSheafPullback318.line e (reconstructed f g e e' square D)))
    (OriginalCanonicalDescent318.datum g (LineSheafUnit318.line S)) :=
  (OriginalCanonicalDescent318.baseChangeInverse f g e' e square
    (reconstructed f g e e' square D)).comp
      ((OriginalSchemeDescentBaseChangeMaps318.map g e' e square
        (AffineMorphismGlobalEffectivity318.hom f D.underlying)).comp
          (trivializationHom f g e e' square D))

@[expose] def coveringIso :
    (Scheme.Modules.pullback g).obj
        ((LineSheafPullback318.line e (reconstructed f g e e' square D)).object) ≅
      (Scheme.Modules.pullback g).obj (LineSheafUnit318.line S).object :=
  ((coverComparison f g e' e square).app
      (reconstructed f g e e' square D).object).symm ≪≫
    (Scheme.Modules.pullback e').mapIso
      (AffineMorphismGlobalEffectivity318.comparison f D.underlying) ≪≫
        D.trivialization ≪≫ (IdentityCotangent318.pullbackUnitIso g).symm

lemma coveringHom_eq : (coveringHom f g e e' square D).sheafHom =
    (coveringIso f g e e' square D).hom := by
  simp only [coveringHom,coveringIso,Hom.comp,OriginalCanonicalDescent318.baseChangeInverse,
    OriginalCanonicalDescent318.inverse,OriginalSchemeDescentBaseChangeMaps318.map,
    AffineMorphismGlobalEffectivity318.hom,trivializationHom,
    Iso.trans_hom,Iso.symm_hom,Iso.app_inv,Functor.mapIso_hom,Category.assoc]
end RigidifiedOriginalDescentData318
