module
public import ActualTwoDescentEllipticModel318
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.Derivative
import all ActualTwoDescentEllipticModel318
public section
noncomputable section
namespace ActualTwoDescentChordPolynomial318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 Polynomial
variable [DecidableEq K]

def cubicPolynomial (n : K) : K[X] := X*(X-C n)*(X+C (3*n))
def chordLine (x y m : K) : K[X] := C m*(X-C x)+C y

/-- The actual group-law chord gives the original monic intersection cubic. -/
theorem actual_chord_polynomial (n x₁ y₁ x₂ y₂ : K)
    (h₁ : (curve n).toAffine.Equation x₁ y₁) (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂)) :
    let m := (curve n).toAffine.slope x₁ x₂ y₁ y₂
    let x₃ := (curve n).toAffine.addX x₁ x₂ m
    cubicPolynomial n-(chordLine x₁ y₁ m)^2=(X-C x₁)*(X-C x₂)*(X-C x₃) := by
  dsimp only
  let m := (curve n).toAffine.slope x₁ x₂ y₁ y₂
  change cubicPolynomial n-(chordLine x₁ y₁ m)^2=
    (X-C x₁)*(X-C x₂)*(X-C ((curve n).toAffine.addX x₁ x₂ m))
  have hmodel : (curve n).toAffine.addPolynomial x₁ y₁ m=
      -(cubicPolynomial n-(chordLine x₁ y₁ m)^2) := by
    rw [WeierstrassCurve.Affine.addPolynomial_eq]
    simp only [Cubic.toPoly,curve,cubicPolynomial,chordLine,map_add,map_sub,map_mul,map_pow,
      map_neg,map_ofNat,map_zero,map_one]
    ring
  have h := WeierstrassCurve.Affine.addPolynomial_slope h₁ h₂ hxy
  change (curve n).toAffine.addPolynomial x₁ y₁ m=
    -((X-C x₁)*(X-C x₂)*(X-C ((curve n).toAffine.addX x₁ x₂ m))) at h
  exact neg_inj.mp (hmodel.symm.trans h)

lemma actual_chord_value (n x y m x₁ x₂ x₃ r : K)
    (h : cubicPolynomial n-(chordLine x y m)^2=(X-C x₁)*(X-C x₂)*(X-C x₃))
    (hr : r*(r-n)*(r+3*n)=0) :
    (x₁-r)*(x₂-r)*(x₃-r)=(m*(r-x)+y)^2 := by
  have he := congrArg (Polynomial.eval r) h
  simp only [cubicPolynomial,chordLine,eval_sub,eval_mul,eval_X,eval_C,eval_add,eval_pow] at he
  rw [hr] at he
  linear_combination he

lemma actual_chord_derivative (n x y m x₁ x₂ x₃ r : K)
    (h : cubicPolynomial n-(chordLine x y m)^2=(X-C x₁)*(X-C x₂)*(X-C x₃)) :
    (3*r^2+4*n*r-3*n^2)-2*m*(m*(r-x)+y)=
      (x₁-r)*(x₂-r)+(x₁-r)*(x₃-r)+(x₂-r)*(x₃-r) := by
  have he := congrArg (fun f : K[X] => Polynomial.eval r (Polynomial.derivative f)) h
  simp only [cubicPolynomial,chordLine,derivative_sub,derivative_mul,derivative_sq,
    derivative_X,derivative_C,derivative_add,eval_sub,eval_mul,eval_X,eval_C,eval_add,
    eval_pow,eval_natCast,eval_one,eval_zero] at he
  linear_combination he

end ActualTwoDescentChordPolynomial318
