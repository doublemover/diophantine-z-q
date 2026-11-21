module
public import CTLiteralisogenyScalarPoints318
public import CTLiteralDualGeometricHom318
import all CTLiteralDualFiberTargetPoints318
import all OriginalCasselsLiteralIsogenyPoint318
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all ActualTwoDescentEllipticModel318
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.LinearCombination
public section
noncomputable section

namespace CTLiteralDualArithmeticHom318

open CTLiteralisogenyScalarPoints318 CTLiteralDualFiberTargetPoints318
open CTLiteralDualFiberCoordinates318 CTLiteralDualGeometricHom318
open OriginalCasselsLiteralIsogenyPoint318 OriginalSelectedCasselsParity318
open OriginalSelectedCasselsLocalArithmetic318
open ActualTwoDescentEllipticModel318

variable {F A : Type*} [Field F] [CharZero F] [Field A] [CharZero A]
  [Algebra F A] [DecidableEq F] [DecidableEq A]
local notation "ι" => (algebraMap F A)

/-- The same reverse point function commutes with the genuine
additive base changes. No unproved naturality of an abstract morphism. -/
theorem dual_base (n : F) (hn : n≠0) (Q : TargetPoint n) :
    sourceBase n (dualPoint n hn Q)=
      dualPoint (ι n) (((map_ne_zero ι).mpr hn)) (targetBase n Q) := by
  cases Q with
  | zero => rw [dual_zero,map_zero,map_zero,dual_zero]
  | some s t h =>
    have he := h.left
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [targetModel,zero_mul,add_zero,zero_add] at he
    have he' : t^2=s*(s^2-4*n*s+16*n^2) := by linear_combination he
    change sourceBase n (dualPoint n hn (targetPoint n s t hn he'))=
      dualPoint (ι n) (((map_ne_zero ι).mpr hn)) (targetBase n (targetPoint n s t hn he'))
    rw [targetBase_point]
    by_cases hs : s=0
    · subst s
      have hz : t=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using he')
      subst t
      rw [show targetPoint n 0 0 hn he'=targetKernel n hn from rfl]
      rw [show targetPoint (ι n) (ι 0) (ι 0) (((map_ne_zero ι).mpr hn)) (map_target_eq n 0 0 he')=
          targetKernel (ι n) (((map_ne_zero ι).mpr hn)) from by
        unfold targetKernel targetPoint
        simp only [map_zero]]
      rw [dual_target_kernel,dual_target_kernel,map_zero]
    rw [dual_affine n s t hn hs he',
      dual_affine (ι n) (ι s) (ι t) (((map_ne_zero ι).mpr hn)) (((map_ne_zero ι).mpr hs)) (map_target_eq n s t he'),
      sourceBase_point]
    unfold point
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor <;> simp only [backX,backY,map_add,map_sub,map_mul,map_div₀,map_pow,map_ofNat]

/-- Same scalar compatibility for the already-accepted forward map. -/
theorem literal_base (n : F) (hn : n≠0) (P : Point n) :
    targetBase n (literalMap n hn P)=
      literalMap (ι n) (((map_ne_zero ι).mpr hn)) (sourceBase n P) := by
  cases P with
  | zero => rw [literal_zero,map_zero,map_zero,literal_zero]
  | some x y h =>
    have he := (curve_equation n x y).mp h.left
    change targetBase n (literalMap n hn (point n x y hn he))=
      literalMap (ι n) (((map_ne_zero ι).mpr hn)) (sourceBase n (point n x y hn he))
    rw [sourceBase_point]
    by_cases hx : x=0
    · subst x
      have hz : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using he)
      subst y
      rw [show point n 0 0 hn he=kernelPoint n hn by unfold kernelPoint; rfl]
      rw [show point (ι n) (ι 0) (ι 0) (((map_ne_zero ι).mpr hn)) (map_source_eq n 0 0 he)=
          kernelPoint (ι n) (((map_ne_zero ι).mpr hn)) from by
        unfold kernelPoint point
        simp only [map_zero]]
      rw [literal_kernel_point,literal_kernel_point,map_zero]
    rw [literal_affine n hn x y hx he,
      literal_affine (ι n) (((map_ne_zero ι).mpr hn)) (ι x) (ι y) (((map_ne_zero ι).mpr hx)) (map_source_eq n x y he)]
    unfold imagePoint
    rw [targetBase_point]
    unfold targetPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor <;> simp only [map_add,map_sub,map_mul,map_div₀,map_pow,map_ofNat]

/-- Transport of the verified geometric reverse addition back to the
same arbitrary characteristic-zero arithmetic field. -/
theorem dual_add (n : F) (hn : n≠0) (P Q : TargetPoint n) :
    dualPoint n hn (P+Q)=dualPoint n hn P+dualPoint n hn Q := by
  let C := AlgebraicClosure F
  letI : DecidableEq C := Classical.decEq _
  apply sourceBase_injective (A:=C) n
  rw [dual_base (A:=C) n hn (P+Q),map_add (targetBase (A:=C) n),dual_geometric_add]
  rw [map_add (sourceBase (A:=C) n),dual_base,dual_base]

def arithmeticDualHom (n : F) (hn : n≠0) : TargetPoint n →+ Point n where
  toFun := dualPoint n hn
  map_zero' := dual_zero n hn
  map_add' := dual_add n hn

theorem literal_dual_add_self_arithmetic (n : F) (hn : n≠0) (Q : TargetPoint n) :
    literalMap n hn (dualPoint n hn Q)=Q+Q := by
  let C := AlgebraicClosure F
  letI : DecidableEq C := Classical.decEq _
  apply targetBase_injective (A:=C) n
  rw [literal_base (A:=C) n hn,dual_base,literal_dual_add_self,map_add]

end CTLiteralDualArithmeticHom318

#print axioms CTLiteralDualArithmeticHom318.dual_base
#print axioms CTLiteralDualArithmeticHom318.arithmeticDualHom
#print axioms CTLiteralDualArithmeticHom318.literal_dual_add_self_arithmetic
