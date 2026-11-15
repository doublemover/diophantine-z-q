module
public import ActualTwoDescentFieldAllTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFieldFullGaloisComparison318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentFieldGaloisCoordinateHom318 ActualTwoDescentFieldAllTorsionGaloisComparison318
open ActualTwoDescentFieldFirstTorsionGaloisComparison318 ActualTwoDescentFieldLastTorsionGaloisComparison318
open ActualTwoDescentFieldNonexceptionalGaloisComparison318

/-- Full actual elliptic Kummer/Galois comparison: infinity and ALL three torsion roots included. -/
theorem actual_full_galois_comparison (n : F) (hn : n ≠ 0) (P : Point n) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd P)=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd P) := by
  cases P with
  | zero => exact actual_zero_galois_comparison n hn
  | some x y h =>
    have hc := (curve_equation n x y).mp h.left
    by_cases hx : x=0
    · subst x
      have hy : y=0 := by
        have hy2 : y^2=0 := by simpa only [zero_mul,mul_zero,sub_self,add_neg_cancel,neg_add_cancel] using hc
        exact pow_eq_zero hy2
      subst y
      exact actual_zero_torsion_galois_comparison n hn
    by_cases hB : x=n
    · subst x
      have hy : y=0 := by
        have hy2 : y^2=0 := by simpa only [zero_mul,mul_zero,sub_self,add_neg_cancel,neg_add_cancel] using hc
        exact pow_eq_zero hy2
      subst y
      exact actual_first_torsion_galois_comparison n hn
    by_cases hA : x= -3*n
    · subst x
      have hy : y=0 := by
        have hz : -3*n+3*n=0 := by ring
        rw [hz,mul_zero] at hc
        exact pow_eq_zero hc
      subst y
      exact actual_last_torsion_galois_comparison n hn
    have hA' : x+3*n ≠ 0 := by intro he; apply hA; linear_combination he
    exact actual_nonexceptional_galois_comparison n x y hn hx (sub_ne_zero.mpr hB) hA' hc

lemma actual_full_galois_hom_identity (n : F) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn=scalarKummerCoordinatesHom n hn := by
  apply MonoidHom.ext
  intro P
  exact actual_full_galois_comparison n hn P.toAdd

end ActualTwoDescentFieldFullGaloisComparison318
