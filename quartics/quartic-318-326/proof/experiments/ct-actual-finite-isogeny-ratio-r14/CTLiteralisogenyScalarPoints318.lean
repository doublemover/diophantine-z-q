module
public import CTLiteralDualTargetAction318
import all ActualTwoDescentEllipticModel318
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTLiteralisogenyScalarPoints318

open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318
open CTLiteralDualTargetAction318 WeierstrassCurve WeierstrassCurve.Affine

variable {F A : Type*} [Field F] [CharZero F] [Field A] [CharZero A]
  [Algebra F A] [DecidableEq F] [DecidableEq A]
local notation "ι" => (algebraMap F A)

private def pointCast {K : Type*} [Field K] [DecidableEq K]
    {W V : WeierstrassCurve.Affine K} (h : W=V) : W.Point ≃+ V.Point := by
  cases h
  exact AddEquiv.refl _

private theorem pointCast_some {K : Type*} [Field K] [DecidableEq K]
    {W V : WeierstrassCurve.Affine K} (h : W=V) (x y : K) (w : W.Nonsingular x y) :
    pointCast h (.some x y w)=
      WeierstrassCurve.Affine.Point.some x y (by simpa only [←h] using w :
        V.Nonsingular x y) := by cases h; rfl

private theorem scalarBaseSelf (W : WeierstrassCurve.Affine F) : W.baseChange F=W := by
  cases W
  rfl

private theorem original_baseChange (n : F) :
    (curve n).toAffine.baseChange A=(curve (ι n)).toAffine := by
  change (curve n).map ι=curve (ι n)
  simp [WeierstrassCurve.map,curve,map_ofNat]

private def scalarPointHom (W : WeierstrassCurve.Affine F)
    (V : WeierstrassCurve.Affine A) (e : W.baseChange A=V) :
    W.Point →+ V.Point :=
  (pointCast e).toAddMonoidHom.comp
    ((WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId F A)).comp
      (pointCast (scalarBaseSelf W).symm).toAddMonoidHom)

private theorem scalarPointHom_injective (W : WeierstrassCurve.Affine F)
    (V : WeierstrassCurve.Affine A) (e : W.baseChange A=V) :
    Function.Injective (scalarPointHom W V e) :=
  (pointCast e).injective.comp
    ((WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId F A)).comp
      (pointCast (scalarBaseSelf W).symm).injective)

private theorem scalarPointHom_some (W : WeierstrassCurve.Affine F)
    (V : WeierstrassCurve.Affine A) (e : W.baseChange A=V) (x y : F)
    (w : W.Nonsingular x y) (v : V.Nonsingular (ι x) (ι y)) :
    scalarPointHom W V e (.some x y w)=.some (ι x) (ι y) v := by
  unfold scalarPointHom
  simp only [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom]
  rw [pointCast_some,WeierstrassCurve.Affine.Point.map_some,pointCast_some] <;> rfl

/-- Actual Mathlib additive point base change for the original cubic. -/
def sourceBase (n : F) : Point n →+ Point (ι n) :=
  scalarPointHom (curve n).toAffine (curve (ι n)).toAffine (original_baseChange n)

/-- Actual Mathlib additive point base change for the literal quotient model. -/
def targetBase (n : F) : TargetPoint n →+ TargetPoint (ι n) :=
  scalarPointHom (targetModel n).toAffine (targetModel (ι n)).toAffine (target_baseChange n)

theorem sourceBase_injective (n : F) : Function.Injective (sourceBase (A:=A) n) :=
  scalarPointHom_injective _ _ _

theorem targetBase_injective (n : F) : Function.Injective (targetBase (A:=A) n) :=
  scalarPointHom_injective _ _ _

theorem map_source_eq (n x y : F) (he : y^2=x*(x-n)*(x+3*n)) :
    (ι y)^2=ι x*(ι x-ι n)*(ι x+3*ι n) := by
  simpa only [map_pow,map_mul,map_add,map_sub,map_ofNat] using congrArg ι he

theorem map_target_eq (n x y : F) (he : y^2=x*(x^2-4*n*x+16*n^2)) :
    (ι y)^2=ι x*((ι x)^2-4*ι n*ι x+16*(ι n)^2) := by
  simpa only [map_pow,map_mul,map_add,map_sub,map_ofNat] using congrArg ι he

theorem sourceBase_point (n x y : F) (hn : n≠0) (he : y^2=x*(x-n)*(x+3*n)) :
    sourceBase n (point n x y hn he)=
      point (ι n) (ι x) (ι y) ((map_ne_zero ι).mpr hn) (map_source_eq n x y he) := by
  unfold sourceBase point
  exact scalarPointHom_some _ _ _ _ _ _ _

theorem targetBase_point (n x y : F) (hn : n≠0) (he : y^2=x*(x^2-4*n*x+16*n^2)) :
    targetBase n (targetPoint n x y hn he)=
      targetPoint (ι n) (ι x) (ι y) ((map_ne_zero ι).mpr hn) (map_target_eq n x y he) := by
  unfold targetBase targetPoint
  exact scalarPointHom_some _ _ _ _ _ _ _

end CTLiteralisogenyScalarPoints318

#print axioms CTLiteralisogenyScalarPoints318.sourceBase_injective
#print axioms CTLiteralisogenyScalarPoints318.targetBase_point
