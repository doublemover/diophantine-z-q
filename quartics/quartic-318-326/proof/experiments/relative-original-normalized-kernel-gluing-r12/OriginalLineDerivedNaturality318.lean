module
public import OriginalLineDerivedPullback318
public section
noncomputable section
namespace OriginalLineDerivedNaturality318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open NonreducedLineRestriction318 SheafInverseImageConstants318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L N : Line Y) (a : L.object ⟶ N.object)
@[expose] def coefficientMap : additive L ⟶ additive N :=
  (SheafOfModules.toSheaf Y.ringCatSheaf).map a
@[expose] def pulledMap : additive (LineSheafPullback318.line f L) ⟶
    additive (LineSheafPullback318.line f N) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullback f).map a)

lemma unit_square : coefficientMap L N a ≫ OriginalLineDerivedPullback318.unit f N =
    OriginalLineDerivedPullback318.unit f L ≫ (directImage f.base).map (pulledMap f L N a) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact congrArg (fun q => q.app U.unop s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)

/-- Naturality of the genuine derived pullback in the ORIGINAL line
morphism, in every degree. No affine cover or quotient enters the proof. -/
lemma naturality (n : ℕ) (x : Sheaf.H (additive L) n) :
    OriginalLineDerivedPullback318.map f N n (Sheaf.H.map (coefficientMap L N a) n x) =
      Sheaf.H.map (pulledMap f L N a) n (OriginalLineDerivedPullback318.map f L n x) := by
  change SourceCohomologyComparison318.comparison f.base _ n
    (Sheaf.H.map (OriginalLineDerivedPullback318.unit f N) n
      (Sheaf.H.map (coefficientMap L N a) n x)) = _
  rw [← Sheaf.H.map_comp_apply,unit_square,Sheaf.H.map_comp_apply]
  exact SourceCohomologyComparison318.comparison_naturality f.base (pulledMap f L N a) n _
end OriginalLineDerivedNaturality318
