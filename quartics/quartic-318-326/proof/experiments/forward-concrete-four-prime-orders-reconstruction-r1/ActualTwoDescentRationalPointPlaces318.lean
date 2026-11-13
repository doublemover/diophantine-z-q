module
public import ActualTwoDescentRationalSquarefree318
public section
noncomputable section
namespace ActualTwoDescentRationalPointPlaces318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentRealKummerSigns318
set_option maxHeartbeats 16000000

/-- An actual rational point with all three original cubic factors nonzero.
This is data supplied by a point, NOT an existence axiom or a Selmer class. -/
structure RationalPoint (n : ℕ) where
  x : ℚ
  y : ℚ
  x_ne : x ≠ 0
  minus_ne : x-n ≠ 0
  plus_ne : x+3*n ≠ 0
  curve : y^2=x*(x-n)*(x+3*n)

/-- The same rational point at a specified completion. -/
def toLocal (q : ℕ) [Fact q.Prime] {n : ℕ} (P : RationalPoint n) : LocalPoint (p:=q) n where
  x := P.x
  y := P.y
  x_ne := by exact_mod_cast P.x_ne
  minus_ne := by exact_mod_cast P.minus_ne
  plus_ne := by exact_mod_cast P.plus_ne
  curve := by exact_mod_cast P.curve

lemma actual_rational_first_positive (n : ℕ) (hn : 0<n) (P : RationalPoint n) : 0<P.x+3*n := by
  have h := actual_real_first_positive (n : ℝ) (P.x : ℝ) (P.y : ℝ)
    (by exact_mod_cast hn) (by exact_mod_cast P.plus_ne) (by exact_mod_cast P.curve)
  exact_mod_cast h

lemma actual_rational_minus_valuation (q : ℕ) [Fact q.Prime] {n : ℕ} (P : RationalPoint n) :
    ((toLocal q P).x-n).valuation=padicValRat q (P.x-n) := by
  have he : (toLocal q P).x-n=((P.x-n : ℚ) : ℚ_[q]) := by push_cast; rfl
  rw [he,Padic.valuation_ratCast]

lemma actual_rational_plus_valuation (q : ℕ) [Fact q.Prime] {n : ℕ} (P : RationalPoint n) :
    ((toLocal q P).x+3*n).valuation=padicValRat q (P.x+3*n) := by
  have he : (toLocal q P).x+3*n=((P.x+3*n : ℚ) : ℚ_[q]) := by push_cast; rfl
  rw [he,Padic.valuation_ratCast]

end ActualTwoDescentRationalPointPlaces318
