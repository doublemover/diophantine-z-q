module
public import ActualTwoDescentAllTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFullGaloisComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentGaloisCoordinateHom318 ActualTwoDescentAllTorsionGaloisComparison318
open ActualTwoDescentFirstTorsionGaloisComparison318 ActualTwoDescentLastTorsionGaloisComparison318
open ActualTwoDescentNonexceptionalGaloisComparison318

/-- Full actual elliptic Kummer/Galois comparison: infinity and ALL three torsion roots included. -/
theorem actual_full_galois_comparison (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd P)=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd P) := by
  cases P with
  | zero => exact actual_zero_galois_comparison n hn
  | some x y h =>
    have hc := (curve_equation n x y).mp h.left
    by_cases hx : x=0
    · subst x
      have hy : y=0 := by nlinarith [hc]
      subst y
      exact actual_zero_torsion_galois_comparison n hn
    by_cases hB : x=n
    · subst x
      have hy : y=0 := by nlinarith [hc]
      subst y
      exact actual_first_torsion_galois_comparison n hn
    by_cases hA : x= -3*n
    · subst x
      have hy : y=0 := by nlinarith [hc]
      subst y
      exact actual_last_torsion_galois_comparison n hn
    have hA' : x+3*n ≠ 0 := by intro he; apply hA; linarith
    exact actual_nonexceptional_galois_comparison n x y hn hx (sub_ne_zero.mpr hB) hA' hc

lemma actual_full_galois_hom_identity (n : ℚ) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn=scalarKummerCoordinatesHom n hn := by
  apply MonoidHom.ext
  intro P
  exact actual_full_galois_comparison n hn P.toAdd

end ActualTwoDescentFullGaloisComparison318
