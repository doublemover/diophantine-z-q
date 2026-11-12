module
public import CartesianFrameModelEquivalence318
public section
noncomputable section
namespace OriginalFrameModelNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFramePathTransport318
universe u
variable {X Y Z Y' Z' : Scheme.{u}} (L : Line X)
  (e : Y ⟶ Z) (e' : Y' ⟶ Z') (u : Y' ⟶ Y) (v : Z' ⟶ Z)
  (f : Y ⟶ X) (g : Z ⟶ X) (f' : Y' ⟶ X) (g' : Z' ⟶ X)
  (he : e ≫ g=f) (he' : e' ≫ g'=f') (hu : u ≫ f=f') (hv : v ≫ g=g')
  (h : e' ≫ v=u ≫ e)
include h in
/-- Native model comparison commutes with the actual coefficient arrow
as an equality of FULL frames, retaining all four original path maps. -/
lemma natural (a : Frames (LineSheafPullback318.line g L)) :
    transport L e' g' f' he' (transport L v g g' hv a)=
      transport L u f f' hu (transport L e g f he a) := by
  rw [composition,composition]
  apply arrow_congr
  exact h
end OriginalFrameModelNaturality318
