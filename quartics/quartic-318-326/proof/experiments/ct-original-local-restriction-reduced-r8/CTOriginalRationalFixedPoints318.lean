module
public import CTOriginalActualEllipticFieldMap318
public import CTOriginalGeometricGaloisAction318
import all CTOriginalEllipticModel318
import all CTOriginalActualEllipticFieldMap318
import all CTOriginalGeometricGaloisAction318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisFixedRational318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentActualEllipticFieldMap318
open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldGaloisPointAction318
local instance : DecidableEq Qbar := Classical.decEq _

def rationalPointMap (n : F) (hn : n ≠ 0) : Point n →+ Point (algebraMap F Qbar n) :=
  ellipticFieldMap (algebraMap F Qbar) n hn

lemma actual_rational_point_fixed (σ : GalQ) (n : F) (hn : n ≠ 0) (P : Point n) :
    galoisPointHom σ n hn (rationalPointMap n hn P)=rationalPointMap n hn P := by
  cases P with
  | zero => rfl
  | some x y h =>
      let s : Qbar ≃ₐ[F] Qbar := σ
      let f : F →+* Qbar := algebraMap F Qbar
      have hx : s (f x) = f x := s.commutes x
      have hy : s (f y) = f y := s.commutes y
      have he : (f y)^2 = f x*(f x-f n)*(f x+3*f n) :=
        ActualTwoDescentEllipticFieldCoordinates318.actual_curve_equation_map f n x y
          ((curve_equation n x y).mp h.left)
      have he' : (s (f y))^2 = s (f x)*(s (f x)-f n)*(s (f x)+3*f n) := by
        rwa [hx,hy]
      change point (f n) (s (f x)) (s (f y)) (rational_parameter_ne n hn) he' =
        point (f n) (f x) (f y) (rational_parameter_ne n hn) he
      simp only [point,WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx,hy⟩

end ActualTwoDescentFieldGaloisFixedRational318
