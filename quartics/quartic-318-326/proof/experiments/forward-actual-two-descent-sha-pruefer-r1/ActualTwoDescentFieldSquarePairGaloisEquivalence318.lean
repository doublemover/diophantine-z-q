module
public import ActualTwoDescentFieldScalarGaloisEquivalence318
public section
noncomputable section
namespace ActualTwoDescentFieldSquarePairGaloisEquivalence318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldScalarGaloisEquivalence318

def squarePairGaloisEquiv : (SquareClass F × SquareClass F) ≃* ((continuousCharacters (F:=F)) × (continuousCharacters (F:=F))) :=
  (scalarGaloisEquiv (F:=F)).prodCongr (scalarGaloisEquiv (F:=F))

lemma actual_squarepair_galois_value (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (squarePairGaloisEquiv (F:=F)) (classOf a ha,classOf b hb)=
      ((scalarConnectingHom (F:=F)) (Units.mk0 a ha),(scalarConnectingHom (F:=F)) (Units.mk0 b hb)) := rfl

/-- A rational squareclass pair is trivial exactly when both actual continuous characters vanish. -/
theorem actual_squarepair_galois_kernel (z : SquareClass F × SquareClass F) :
    (squarePairGaloisEquiv (F:=F)) z=1 ↔ z=1 := by
  constructor
  · intro h
    apply (squarePairGaloisEquiv (F:=F)).injective
    exact h.trans (squarePairGaloisEquiv (F:=F)).map_one.symm
  · rintro rfl
    exact (squarePairGaloisEquiv (F:=F)).map_one

end ActualTwoDescentFieldSquarePairGaloisEquivalence318
