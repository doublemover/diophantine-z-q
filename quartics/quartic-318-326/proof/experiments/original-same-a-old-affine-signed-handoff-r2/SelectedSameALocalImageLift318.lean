module

public import SelectedSameALiteralInjectiveRow318

/-!
# The original local lift gives a local lift of the same image section

No new affine lifting or quotient-section surjectivity is assumed.
This uses the right square of the actual injective row comparison.
-/

public section

open CategoryTheory Opposite

namespace SelectedSameALocalImageLift318

universe u

open SelectedSameALiteralInjectiveRow318

variable (X : TopCat.{u})
variable {S : ShortComplex (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})}
variable {L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The original lift on W maps to a true lift on that same W of
the restriction of the one global image used by boundary_eq. -/
theorem factor_local_lift (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L)
    (W : TopologicalSpace.Opens X)
    (z : S.X₃.obj.obj (op (⊤ : TopologicalSpace.Opens X)))
    (t : S.X₂.obj.obj (op W))
    (ht : S.g.hom.app (op W) t =
      S.X₃.obj.map (homOfLE (show W ≤ ⊤ from le_top)).op z) :
    (target X L).g.hom.app (op W) ((factor X hOld lambdaA).τ₂.hom.app (op W) t) =
      (target X L).X₃.obj.map (homOfLE (show W ≤ ⊤ from le_top)).op
        ((factor X hOld lambdaA).τ₃.hom.app (op (⊤ : TopologicalSpace.Opens X)) z) := by
  let f := factor X hOld lambdaA
  let r := (homOfLE (show W ≤ ⊤ from le_top)).op
  let vW := f.τ₃.hom.app (op W)
  have hc := congrArg
    (fun m : S.X₂ ⟶ (target X L).X₃ => m.hom.app (op W) t) f.comm₂₃
  change (target X L).g.hom.app (op W) (f.τ₂.hom.app (op W) t) =
    vW (S.g.hom.app (op W) t) at hc
  have hn := congrArg
    (fun m : S.X₃.obj.obj (op (⊤ : TopologicalSpace.Opens X)) ⟶
      (target X L).X₃.obj.obj (op W) => m z)
    (f.τ₃.hom.naturality r)
  change vW (S.X₃.obj.map r z) =
    (target X L).X₃.obj.map r (f.τ₃.hom.app (op (⊤ : TopologicalSpace.Opens X)) z) at hn
  exact hc.trans ((congrArg (fun v => vW v) ht).trans hn)

end SelectedSameALocalImageLift318
