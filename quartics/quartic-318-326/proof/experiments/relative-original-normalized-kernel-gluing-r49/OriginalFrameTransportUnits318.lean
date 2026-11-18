module
public import OriginalFramePullbackUnits318
public section
noncomputable section
namespace OriginalFrameTransportUnits318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L M : Line X) (h : L.object ≅ M.object)

lemma action (u : Γ(X,⊤)ˣ) (e : Frames L) :
    act L u e ≪≫ h=act M u (e ≪≫ h) := by
  apply Iso.ext
  simp only [act,Iso.trans_hom,Category.assoc]

/-- The actual ratio is unchanged by an arbitrary full target-line
comparison, including the original coefficient pullback associator. -/
lemma ratio (e d : Frames L) :
    OriginalLineFrameUnitTorsor318.ratio M (e ≪≫ h) (d ≪≫ h)=
      OriginalLineFrameUnitTorsor318.ratio L e d := by
  have he := congrArg (fun k => k ≪≫ h) (ratio_act L e d)
  rw [action] at he
  rw [←he,act_ratio]
end OriginalFrameTransportUnits318
