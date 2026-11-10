module
public import RelativeOriginalPolynomialAlgebra318
public import OriginalLineFiniteFlatPID318
public section
noncomputable section
namespace RelativeOriginalChartSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (k R B : CommRingCat.{u})
  [Algebra k R] [Algebra k B] [Algebra (Polynomial k) B]
  [IsScalarTower k (Polynomial k) B] [Module.Finite (Polynomial k) B]
  (L : Line (Spec (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original k R B))))

/-- Actual original line sections on the original coefficient-tensor chart,
with scalars restricted along its proved original polynomial coordinate map. -/
abbrev sections := OriginalLineFiniteFlatPID318.pushed (CommRingCat.of (Polynomial R))
  (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original k R B)) L

/-- Every original line on this actual base-changed chart has finite
polynomial sections, even for nonreduced/non-Noetherian coefficient rings.
No free basis or PID argument is used. -/
instance finite : Module.Finite (Polynomial R) (sections k R B L) :=
  OriginalLineFiniteFlatPID318.finite (CommRingCat.of (Polynomial R))
    (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original k R B)) L

lemma scalar (p : Polynomial R) (m : sections k R B L) :
    p • m = (RelativeOriginalPolynomialAlgebra318.polynomialMap k R B p) •
      (m : OriginalLineAffineModel318.sections
        (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original k R B)) L) :=
  ModuleCat.restrictScalars.smul_def
    (RelativeOriginalPolynomialAlgebra318.polynomialMap k R B) p m
end RelativeOriginalChartSections318
