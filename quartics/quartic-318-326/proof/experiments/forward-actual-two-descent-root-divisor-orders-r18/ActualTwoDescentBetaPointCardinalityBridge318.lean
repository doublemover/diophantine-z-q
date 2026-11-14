module
public import ActualTwoDescentBetaNonexceptional318
public section
noncomputable section
namespace ActualTwoDescentBetaPointCardinalityBridge318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentKummerHom318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentEightClassCube318 ActualTwoDescentSameRationalBounds318
open ActualTwoDescentQuotientCardinalitySurjectivity318 ActualTwoDescentBetaNonexceptional318
open ActualTwoDescentEllipticPointExtraction318 ActualTwoDescentPointExtraction318
open ActualTwoDescentTorsionKummerValues318

/-- This is the explicit remaining cardinality-to-point bridge: an ACTUAL
quotient with eight elements supplies an actual nonzero rational beta point.
No equality of quotient cardinality is assumed to follow from local counts. -/
theorem actual_beta_point_of_quotient_eight (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (hcard : Nat.card (DoubleQuotient (n : ℚ))=8) :
    Nonempty (KummerPoint (b : ℚ) (n : ℚ)) := by
  let hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  let hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  obtain ⟨P,hP⟩ := actual_cube_represented_of_eight n b hn hb H hcard (0,0,1)
  obtain ⟨x,y,h,hxy,hx,hB,hA⟩ := actual_beta_nonexceptional (n : ℚ) (b : ℚ) hnq hbq
    (actual_cube_injective_of_eight n b hn hb H hcard) P hP
  subst P
  have hclass : kummerClass (n : ℚ) hnq (.some x y h)=(classOf (b : ℚ) hbq,1) := by
    simpa [cubeClass,retainedBetaClass] using hP
  obtain ⟨Q,hQx,hQy⟩ := actual_kummer_point_of_elliptic_class (n : ℚ) (b : ℚ) x y hnq hbq h hx hA hB hclass
  exact ⟨Q⟩

end ActualTwoDescentBetaPointCardinalityBridge318
