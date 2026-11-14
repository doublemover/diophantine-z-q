module
public import ActualTwoDescentLiteralKummerClasses318
public section
noncomputable section
namespace ActualTwoDescentEllipticPointExtraction318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentKummerHom318 ActualTwoDescentLiteralKummerClasses318
open ActualTwoDescentPointExtraction318

/-- A represented beta class in the ACTUAL rational elliptic group yields
the original rational KummerPoint with exactly the same x,y and parameter.
The class representation remains an input; no global point existence is inferred. -/
theorem actual_kummer_point_of_elliptic_class (n beta x y : ℚ) (hn : n ≠ 0) (hb : beta ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hA : x+3*n ≠ 0) (hB : x-n ≠ 0)
    (H : kummerClass n hn (.some x y h)=(classOf beta hb,1)) :
    ∃ P : KummerPoint beta n, P.x=x ∧ P.y=y := by
  have H' : kummerClass n hn (.some x y h)=(classOf beta hb,classOf (1 : ℚ) one_ne_zero) := by
    simpa only [class_of_one] using H
  obtain ⟨u,v,hu,hv,hU,hV⟩ := (actual_kummer_pair_iff n x y beta 1 hn h hA hB hb one_ne_zero).mp H'
  refine ⟨⟨x,y,u,v,hx,hu,hv,(curve_equation n x y).mp h.left,hU,?_⟩,rfl,rfl⟩
  simpa only [one_mul] using hV

end ActualTwoDescentEllipticPointExtraction318
