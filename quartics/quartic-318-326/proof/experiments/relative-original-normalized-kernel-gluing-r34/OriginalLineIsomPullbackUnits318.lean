module
public import OriginalModulePullbackScalar318
public import OriginalFramePullbackUnits318
public section
noncomputable section
namespace OriginalLineIsomPullbackUnits318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L K : Line Y)
local notation "A" => LineSheafPullback318.line f L
local notation "B" => LineSheafPullback318.line f K
lemma action (u : Γ(Y,⊤)ˣ) (e : L.object ≅ K.object) :
    (Scheme.Modules.pullback f).mapIso (OriginalLineIsomUnitTorsor318.act L K u e)=
      OriginalLineIsomUnitTorsor318.act A B (OriginalFramePullbackUnits318.units f u)
        ((Scheme.Modules.pullback f).mapIso e) := by
  apply Iso.ext
  change (Scheme.Modules.pullback f).map (ModuleScalar318.map L.object (u:Γ(Y,⊤)) ≫ e.hom)=_
  rw [Functor.map_comp,OriginalModulePullbackScalar318.pullback]
  rfl
/-- Full original isomorphism ratios commute with arbitrary coefficient
pullback, including nonflat/nonreduced tests and their native unit maps. -/
lemma ratio (e d : L.object ≅ K.object) :
    OriginalLineIsomUnitTorsor318.ratio A B ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)=
      OriginalFramePullbackUnits318.units f (OriginalLineIsomUnitTorsor318.ratio L K e d) := by
  have h := congrArg ((Scheme.Modules.pullback f).mapIso)
    (OriginalLineIsomUnitTorsor318.ratio_act L K e d)
  rw [action] at h
  rw [←h,OriginalLineIsomUnitTorsor318.act_ratio]
end OriginalLineIsomPullbackUnits318
