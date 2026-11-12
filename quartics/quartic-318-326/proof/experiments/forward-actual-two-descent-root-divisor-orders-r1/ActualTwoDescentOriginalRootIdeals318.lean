module
public import ActualTwoDescentOriginalPerfectPairing318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentEllipticModel318 WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open scoped nonZeroDivisors
variable {K : Type*} [Field K] [CharZero K]

/-- The three ACTUAL affine roots, not sign-coordinate placeholders. -/
def root (n : K) : Fin 3 → K := ![0,n,-3*n]

lemma actual_root_equation (n : K) (i : Fin 3) :
    (0 : K)^2=root n i*(root n i-n)*(root n i+3*n) := by
  fin_cases i <;> simp [root]

lemma actual_root_nonsingular (n : K) (hn : n ≠ 0) (i : Fin 3) :
    (curve n).toAffine.Nonsingular (root n i) 0 :=
  curve_nonsingular n _ _ hn (actual_root_equation n i)

def rootPoint (n : K) (hn : n ≠ 0) (i : Fin 3) : Point n :=
  point n (root n i) 0 hn (actual_root_equation n i)

def rootIdeal (n : K) (i : Fin 3) : Ideal (curve n).toAffine.CoordinateRing :=
  XYIdeal (curve n).toAffine (root n i) 0

/-- A genuine equality of original affine coordinate-ring ideals:
(x-a,y)^2=(x-a). It is NOT yet a projective divisor formula at infinity. -/
theorem actual_root_ideal_square (n : K) (hn : n ≠ 0) (i : Fin 3) :
    rootIdeal n i*rootIdeal n i=XIdeal (curve n).toAffine (root n i) := by
  have h := XYIdeal_neg_mul (actual_root_nonsingular n hn i)
  simpa only [curve_negY,neg_zero,Polynomial.C_0,rootIdeal] using h

/-- The ideal is an actual unit in the native fractional-ideal group of
the original function field; invertibility is produced from smoothness. -/
def rootFractionalIdeal (n : K) (hn : n ≠ 0) (i : Fin 3) :
    (FractionalIdeal (curve n).toAffine.CoordinateRing⁰ (curve n).toAffine.FunctionField)ˣ :=
  XYIdeal' (actual_root_nonsingular n hn i)

lemma actual_root_fractional_ideal_value (n : K) (hn : n ≠ 0) (i : Fin 3) :
    (rootFractionalIdeal n hn i :
      FractionalIdeal (curve n).toAffine.CoordinateRing⁰ (curve n).toAffine.FunctionField)=
      (rootIdeal n i : FractionalIdeal (curve n).toAffine.CoordinateRing⁰
        (curve n).toAffine.FunctionField) := by
  simp only [rootFractionalIdeal,XYIdeal'_eq,Polynomial.C_0,rootIdeal]

lemma actual_root_class_nonzero (n : K) (i : Fin 3) :
    XClass (curve n).toAffine (root n i) ≠ 0 := XClass_ne_zero _

end ActualTwoDescentOriginalRootIdeals318
