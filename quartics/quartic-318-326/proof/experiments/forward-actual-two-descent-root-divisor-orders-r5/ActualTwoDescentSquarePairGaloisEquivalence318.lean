module
public import ActualTwoDescentScalarGaloisEquivalence318
public section
noncomputable section
namespace ActualTwoDescentSquarePairGaloisEquivalence318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentScalarConnectingHom318
open ActualTwoDescentScalarGaloisEquivalence318

def squarePairGaloisEquiv : (SquareClass ℚ × SquareClass ℚ) ≃* (continuousCharacters × continuousCharacters) :=
  scalarGaloisEquiv.prodCongr scalarGaloisEquiv

lemma actual_squarepair_galois_value (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    squarePairGaloisEquiv (classOf a ha,classOf b hb)=
      (scalarConnectingHom (Units.mk0 a ha),scalarConnectingHom (Units.mk0 b hb)) := rfl

/-- A rational squareclass pair is trivial exactly when both actual continuous characters vanish. -/
theorem actual_squarepair_galois_kernel (z : SquareClass ℚ × SquareClass ℚ) :
    squarePairGaloisEquiv z=1 ↔ z=1 := by
  constructor
  · intro h
    apply squarePairGaloisEquiv.injective
    exact h.trans squarePairGaloisEquiv.map_one.symm
  · rintro rfl
    exact squarePairGaloisEquiv.map_one

end ActualTwoDescentSquarePairGaloisEquivalence318
