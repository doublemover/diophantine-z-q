module

public import SelectedSameALiteralInjectiveRow318

/-!
# Image of the actual signed coefficient on the same open

Evaluate the existing injective row comparison on one open, in the
application the literal intersection of two old affine charts. The only
coefficient premise is its old defining equation, right minus left.
-/

public section

open CategoryTheory Opposite

namespace SelectedSameASignedOpenInjectiveImage318

universe u

open SelectedSameALiteralInjectiveRow318

variable (X : TopCat.{u})
variable {S : ShortComplex (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})}
variable {L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The existing comparison takes the old signed coefficient to the
actual contracted coefficient. Both image lifts stay on the same open. -/
theorem factor_right_minus_left (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L)
    (W : TopologicalSpace.Opens X) (b : S.X₁.obj.obj (op W))
    (left right : S.X₂.obj.obj (op W))
    (hb : S.f.hom.app (op W) b = right - left) :
    (target X L).f.hom.app (op W) (lambdaA.hom.app (op W) b) =
      (factor X hOld lambdaA).τ₂.hom.app (op W) right -
      (factor X hOld lambdaA).τ₂.hom.app (op W) left := by
  let f := factor X hOld lambdaA
  let eW := (target X L).f.hom.app (op W)
  let sW := f.τ₂.hom.app (op W)
  have hleft : f.τ₁.hom.app (op W) b = lambdaA.hom.app (op W) b :=
    congrArg (fun m : S.X₁ ⟶ L => m.hom.app (op W) b) (factor_left X hOld lambdaA)
  have hsquare := congrArg
    (fun m : S.X₁ ⟶ (target X L).X₂ => m.hom.app (op W) b) f.comm₁₂
  change eW (f.τ₁.hom.app (op W) b) = sW (S.f.hom.app (op W) b) at hsquare
  change eW (lambdaA.hom.app (op W) b) = sW right - sW left
  calc
    _ = eW (f.τ₁.hom.app (op W) b) := congrArg (fun x => eW x) hleft.symm
    _ = sW (S.f.hom.app (op W) b) := hsquare
    _ = sW (right - left) := congrArg (fun x => sW x) hb
    _ = sW right - sW left := sW.hom.map_sub right left

end SelectedSameASignedOpenInjectiveImage318
