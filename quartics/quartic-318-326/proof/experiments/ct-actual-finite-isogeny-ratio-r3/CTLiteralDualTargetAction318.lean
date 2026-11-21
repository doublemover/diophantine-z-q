module
public import CTLiteralDualFiberTargetPoints318
import all OriginalSelectedCasselsParity318
import all CTLiteralDualFiberTargetPoints318
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTLiteralDualTargetAction318

open WeierstrassCurve WeierstrassCurve.Affine
open OriginalSelectedCasselsParity318 CTLiteralDualFiberTargetPoints318

variable {F A : Type*} [Field F] [CharZero F] [Field A] [CharZero A]
  [Algebra F A] [DecidableEq A]

/-- The genuine Mathlib base change of this literal target model,
identified with the same scalar-parameter target curve. -/
theorem target_baseChange (n : F) :
    (targetModel n).toAffine.baseChange A =
      (targetModel (algebraMap F A n)).toAffine := by
  change (targetModel n).map (algebraMap F A) = targetModel (algebraMap F A n)
  simp [WeierstrassCurve.map,targetModel,map_ofNat]

private def pointModelEquiv {W V : WeierstrassCurve.Affine A} (e : W=V) :
    W.Point ≃+ V.Point := by
  cases e
  exact AddEquiv.refl _

private theorem pointModelEquiv_symm {W V : WeierstrassCurve.Affine A} (e : W=V) :
    (pointModelEquiv e).symm=pointModelEquiv e.symm := by
  cases e
  rfl

private theorem pointModelEquiv_some {W V : WeierstrassCurve.Affine A} (e : W=V)
    (x y : A) (hx : W.Nonsingular x y) :
    pointModelEquiv e (.some x y hx)=
      WeierstrassCurve.Affine.Point.some x y (by simpa only [←e] using hx :
        V.Nonsingular x y) := by
  cases e
  rfl

/-- Actual additive action, using the pinned additive Point.map
on the true base-changed curve, not a new coordinate group law. -/
def targetAction (n : F) (σ : A ≃ₐ[F] A) :
    TargetPoint (algebraMap F A n) →+ TargetPoint (algebraMap F A n) :=
  let e := pointModelEquiv (target_baseChange (A:=A) n)
  e.toAddMonoidHom.comp ((WeierstrassCurve.Affine.Point.map
    (W' := (targetModel n).toAffine) σ.toAlgHom).comp e.symm.toAddMonoidHom)

theorem map_target_equation (n : F) (σ : A ≃ₐ[F] A) (s t : A)
    (h : t^2=s*(s^2-4*algebraMap F A n*s+16*(algebraMap F A n)^2)) :
    (σ t)^2=σ s*((σ s)^2-4*algebraMap F A n*(σ s)+16*(algebraMap F A n)^2) := by
  have he := congrArg σ h
  simpa only [map_add,map_sub,map_mul,map_pow,map_ofNat,σ.commutes] using he

theorem targetAction_on_point (n : F) (σ : A ≃ₐ[F] A) (hn : algebraMap F A n≠0)
    (s t : A) (h : t^2=s*(s^2-4*algebraMap F A n*s+16*(algebraMap F A n)^2)) :
    targetAction n σ (targetPoint (algebraMap F A n) s t hn h) =
      targetPoint (algebraMap F A n) (σ s) (σ t) hn (map_target_equation n σ s t h) := by
  simp only [targetAction,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    pointModelEquiv_symm,targetPoint]
  rw [pointModelEquiv_some,WeierstrassCurve.Affine.Point.map_some,pointModelEquiv_some] <;> rfl

theorem targetAction_fixes_kernel (n : F) (σ : A ≃ₐ[F] A) (hn : algebraMap F A n≠0) :
    targetAction n σ (targetKernel (algebraMap F A n) hn)=targetKernel (algebraMap F A n) hn := by
  change targetAction n σ (targetPoint (algebraMap F A n) 0 0 hn (by simp)) =
    targetPoint (algebraMap F A n) 0 0 hn (by simp)
  rw [targetAction_on_point]
  unfold targetPoint
  simp only [map_zero]

end CTLiteralDualTargetAction318

#print axioms CTLiteralDualTargetAction318.targetAction_on_point
