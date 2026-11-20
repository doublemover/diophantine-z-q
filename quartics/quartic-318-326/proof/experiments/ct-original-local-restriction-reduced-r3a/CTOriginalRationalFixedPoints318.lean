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
  | some x y h => simp only [rationalPointMap,ellipticFieldMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      pointMap,galoisPointHom,galoisPoint,point,σ.commutes]

end ActualTwoDescentFieldGaloisFixedRational318
