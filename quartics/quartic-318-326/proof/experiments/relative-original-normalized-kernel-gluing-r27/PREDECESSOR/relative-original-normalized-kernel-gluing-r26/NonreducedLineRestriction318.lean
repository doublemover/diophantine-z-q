module
public import NonreducedAffineLineHOne318
public import OpenImmersionAdditiveRestriction318
public import LineSheafPullback318
public section
noncomputable section
namespace NonreducedLineRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open LocalSheafCohomologySections318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The additive sheaf of the SAME original line on any scheme. -/
abbrev additive (L : Line Y) : ASheaf (X:=Y) :=
  (SheafOfModules.toSheaf Y.ringCatSheaf).obj L.object

/-- Both restrictions evaluate on the SAME original image opens; forgetting
the changed scalar action retains the original section/restriction maps. -/
def restrictionIso (M : Y.Modules) :
    (OpenImmersionAdditiveRestriction318.restriction f).obj
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) ≅
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((Scheme.Modules.restrictFunctor f).obj M) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V h; rfl))

/-- The original line pullback is identified with its actual additive open
restriction, through the original canonical module restriction comparison. -/
def pullbackIso (L : Line Y) :
    (OpenImmersionAdditiveRestriction318.restriction f).obj (additive L) ≅
      additive (LineSheafPullback318.line f L) :=
  restrictionIso f L.object ≪≫
    (SheafOfModules.toSheaf X.ringCatSheaf).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L.object)
end NonreducedLineRestriction318
